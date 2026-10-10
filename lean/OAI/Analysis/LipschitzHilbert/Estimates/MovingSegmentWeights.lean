import OAI.Analysis.LipschitzHilbert.Estimates.MovingWeightBudget
import OAI.Analysis.LipschitzHilbert.Estimates.MovingSegmentLogs
import OAI.Analysis.LipschitzHilbert.Estimates.TopMovingLogAbsorption

namespace OAI

/-! Endpoint weight motion from the relative parent and boundary losses.
The full-root loss is used only at the snapshot. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem segmentLog_re_le_of_log_motion (n n' R' : ℕ → ℝ) (phase : ℕ → ℂ)
    (a δ lower : ℝ) (start k : ℕ) (ha : 0 ≤ a) (hlower : 0 < lower)
    (hn : lower ≤ n k) (hmove : |Real.log (n' k)-Real.log (n k)| ≤ δ)
    (hR : ∀ i < k, 0 ≤ R' i) (hz : ∀ i < k, 0 ≤ (phase i).re) :
    (segmentLog n' R' phase a start k).re ≤ a*δ-a*Real.log lower := by
  have hlog := Real.log_le_log hlower hn
  have hlow : Real.log lower-δ ≤ Real.log (n' k) := by
    have hm := (abs_le.mp hmove).1
    linarith
  have hsum : 0 ≤ ∑ i ∈ Finset.Ico start k, (phase i).re*R' i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hz i (Finset.mem_Ico.mp hi).2)
      (hR i (Finset.mem_Ico.mp hi).2))
  simp only [segmentLog, Complex.sub_re, Complex.ofReal_re, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith

/-- The moving endpoint-plus-variation estimate on any later segment.
All error factors multiply the original loss budget, never the depth. -/
theorem moving_segmentWeight_variation (n n' R R' : ℕ → ℝ) (phase : ℕ → ℂ)
    (start N K : ℕ) (hstart : start ≤ N) (a Z δ ε lower : ℝ)
    (ha : 0 ≤ a) (hZ : 0 ≤ Z) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hlower : 0 < lower)
    (hn : ∀ j ≤ N, lower ≤ n j) (hn' : ∀ j ≤ N, 0 < n' j)
    (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j) (hR0' : ∀ j < N, 0 ≤ R' j)
    (hR : ∀ j < N, R j ≤ Real.log (n (j+1-K)/n (j+1)))
    (hz0 : ∀ j < N, 0 ≤ (phase j).re) (hz : ∀ j < N, ‖phase j‖ ≤ Z)
    (hmass : ∀ j, start ≤ j → j ≤ N → |Real.log (n' j)-Real.log (n j)| ≤ δ)
    (hPmove : ∀ j ∈ Finset.Ico start N,
      |Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1))| ≤ ε*Real.log (n j/n (j+1)))
    (hRmove : ∀ j ∈ Finset.Ico start N, |R' j-R j| ≤ ε*R j) :
    let V := (a+Z*K)*Real.log (n 0/n N)
    ‖segmentWeight n' R' phase a start N-segmentWeight n R phase a start N‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖(segmentWeight n' R' phase a start (j+1)-segmentWeight n R phase a start (j+1))-
          (segmentWeight n' R' phase a start j-segmentWeight n R phase a start j)‖) ≤
      (Real.exp (a*δ)*lower^(-a))*((a*δ+ε*V)+ε*V+(a*δ+ε*V)*V) := by
  dsimp only
  let V := (a+Z*K)*Real.log (n 0/n N)
  have hn0 (j : ℕ) (hj : j ≤ N) : 0 < n j := hlower.trans_le (hn j hj)
  have hparent (j : ℕ) (hj : j < N) : n (j+1) ≤ n j :=
    hmono (by change j ≤ N; omega) (by change j+1 ≤ N; omega) (by omega)
  have hlog : 0 ≤ Real.log (n 0/n N) :=
    Real.log_nonneg ((one_le_div (hn0 N le_rfl)).mpr
      (hmono (by change 0 ≤ N; omega) (by change N ≤ N; omega) (Nat.zero_le N)))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hL (j : ℕ) (_hj : start ≤ j) (hjN : j ≤ N) :
      (segmentLog n R phase a start j).re ≤ a*δ-a*Real.log lower := by
    apply (segmentLog_re_le n R phase a lower start j ha hlower (hn j hjN)
      (fun i hi => hR0 i (hi.trans_le hjN))
      (fun i hi => hz0 i (hi.trans_le hjN))).trans
    nlinarith
  have hM (j : ℕ) (hj : start ≤ j) (hjN : j ≤ N) :
      (segmentLog n' R' phase a start j).re ≤ a*δ-a*Real.log lower :=
    segmentLog_re_le_of_log_motion n n' R' phase a δ lower start j ha hlower (hn j hjN)
      (hmass j hj hjN) (fun i hi => hR0' i (hi.trans_le hjN))
      (fun i hi => hz0 i (hi.trans_le hjN))
  have h := exponential_weight_motion_on_interval
    (segmentLog n R phase a start) (segmentLog n' R' phase a start)
    (segmentCost n R a Z) start N hstart (a*δ-a*Real.log lower) (a*δ) ε V
    (mul_nonneg ha hδ) hε hV hL hM
    (segmentLog_initial_motion n n' R R' phase a δ start ha (hmass start le_rfl hstart))
    (fun j hj => segmentCost_nonnegative n R a Z j ha hZ
      (hn0 (j+1) (by have := (Finset.mem_Ico.mp hj).2; omega))
      (hparent j (Finset.mem_Ico.mp hj).2) (hR0 j (Finset.mem_Ico.mp hj).2))
    (fun j hj => segmentLog_increment_le_cost n R phase a Z start j
      (Finset.mem_Ico.mp hj).1 ha hZ
      (hn0 (j+1) (by have := (Finset.mem_Ico.mp hj).2; omega))
      (hparent j (Finset.mem_Ico.mp hj).2) (hR0 j (Finset.mem_Ico.mp hj).2)
      (hz j (Finset.mem_Ico.mp hj).2))
    (fun j hj => segmentLog_increment_motion n n' R R' phase a ε Z start j
      (Finset.mem_Ico.mp hj).1 ha hZ
      (hn0 j (Nat.le_of_lt (Finset.mem_Ico.mp hj).2))
      (hn0 (j+1) (by have := (Finset.mem_Ico.mp hj).2; omega))
      (hn' j (Nat.le_of_lt (Finset.mem_Ico.mp hj).2))
      (hn' (j+1) (by have := (Finset.mem_Ico.mp hj).2; omega))
      (hPmove j hj) (hRmove j hj) (hz j (Finset.mem_Ico.mp hj).2))
    (segmentCost_sum_le_full_root n R start N K a Z ha hZ hn0 hmono hR0 hR)
  have heq : Real.exp (a*δ-a*Real.log lower) = Real.exp (a*δ)*lower^(-a) := by
    rw [Real.rpow_def_of_pos hlower, ← Real.exp_add]
    congr 1
    ring
  simpa only [segmentWeight, heq] using h

end LipschitzHilbert

end

end OAI
