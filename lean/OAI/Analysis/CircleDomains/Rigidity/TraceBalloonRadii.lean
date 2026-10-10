import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonDensity
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! Explicit shrinking balloon radii. The geometric extra radii reserve
at least half of every zero-radius balloon after all later deletions. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 def traceExtraRadius (j : ℕ) : ℝ := (1/2:ℝ)^j

 theorem traceExtraRadius_pos (j : ℕ) : 0 < traceExtraRadius j := by
  exact pow_pos (by norm_num) j

 theorem traceExtraRadius_sq (j : ℕ) : traceExtraRadius j^2 = (1/4:ℝ)^j := by
  dsimp only [traceExtraRadius]
  rw [← pow_mul,Nat.mul_comm,pow_mul]
  norm_num

 theorem traceExtraRadius_summable_sq : Summable (fun j => traceExtraRadius j^2) := by
  simp_rw [traceExtraRadius_sq]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

 theorem traceExtraRadius_tail (j : ℕ) :
    (∑' k : ℕ, traceExtraRadius (k+j+1)^2) = traceExtraRadius j^2/3 := by
  simp_rw [traceExtraRadius_sq,show ∀ k : ℕ, (1/4:ℝ)^(k+j+1) = (1/4)^k*((1/4)^j/4) by
    intro k; rw [pow_add,pow_succ]; ring]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)]
  ring

 def traceBalloonRadius (r : ℕ → ℝ) (m j : ℕ) : ℝ :=
  if 0 < r j then (1+1/((m:ℝ)+1))*r j else traceExtraRadius j/((m:ℝ)+1)

 theorem traceBalloonRadius_pos {r : ℕ → ℝ} (m j : ℕ) :
    0 < traceBalloonRadius r m j := by
  dsimp only [traceBalloonRadius]
  split_ifs with h
  · exact mul_pos (by positivity) h
  · exact div_pos (traceExtraRadius_pos j) (by positivity)

 theorem traceBalloonRadius_lt {r : ℕ → ℝ} (hr : ∀ j, 0 ≤ r j) (m j : ℕ) :
    r j < traceBalloonRadius r m j := by
  dsimp only [traceBalloonRadius]
  split_ifs with h
  · have : 0 < (1/((m:ℝ)+1))*r j := mul_pos (by positivity) h
    nlinarith
  · have hr0 : r j = 0 := le_antisymm (le_of_not_gt h) (hr j)
    rw [hr0]
    exact div_pos (traceExtraRadius_pos j) (by positivity)

 theorem traceBalloonRadius_le_double {r : ℕ → ℝ} (m j : ℕ) (hr : 0 < r j) :
    traceBalloonRadius r m j ≤ 2*r j := by
  dsimp only [traceBalloonRadius]
  rw [ite_eq_left hr]
  have hi : 1/((m:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  nlinarith

 theorem traceBalloonRadius_summable_sq {r : ℕ → ℝ}
    (hr : Summable (fun j => r j^2)) (m : ℕ) :
    Summable (fun j => traceBalloonRadius r m j^2) := by
  apply ((hr.mul_left 4).add traceExtraRadius_summable_sq).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro j
  by_cases hj : 0 < r j
  · have h := traceBalloonRadius_le_double m j hj
    have hs := pow_le_pow_left₀ (traceBalloonRadius_pos m j).le h 2
    nlinarith [sq_nonneg (traceExtraRadius j)]
  · have hi : traceBalloonRadius r m j ≤ traceExtraRadius j := by
      simp only [traceBalloonRadius,ite_eq_right hj]
      exact (div_le_self (traceExtraRadius_pos j).le (by
        have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith))
    have hs := pow_le_pow_left₀ (traceBalloonRadius_pos m j).le hi 2
    nlinarith [sq_nonneg (r j)]

 theorem traceBalloonRadius_tendsto {r : ℕ → ℝ} (hr : ∀ j, 0 ≤ r j) (j : ℕ) :
    Tendsto (fun m => traceBalloonRadius r m j) atTop (𝓝 (r j)) := by
  by_cases hj : 0 < r j
  · have h := ((tendsto_const_nhds (x := (1:ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const (r j)
    simpa only [traceBalloonRadius,ite_eq_left hj,add_zero,one_mul] using h
  · have hr0 : r j = 0 := le_antisymm (le_of_not_gt hj) (hr j)
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (traceExtraRadius j)
    simpa only [traceBalloonRadius,hr0,lt_self_iff_false,ite_false,div_eq_mul_inv,one_div,one_mul,mul_zero] using h

 theorem traceBalloonRadius_zero_tail {r : ℕ → ℝ} (m j : ℕ) (hrj : r j = 0) :
    (∑' k : ℕ, (if r (k+j+1) = 0 then traceBalloonRadius r m (k+j+1) else 0)^2) ≤
      traceBalloonRadius r m j^2/2 := by
  have hs0 : Summable (fun k : ℕ => traceExtraRadius (k+j+1)^2) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (j+1)).mpr traceExtraRadius_summable_sq
  have hs : Summable (fun k : ℕ => traceExtraRadius (k+j+1)^2/((m:ℝ)+1)^2) := hs0.div_const _
  have hp (k : ℕ) : (if r (k+j+1) = 0 then traceBalloonRadius r m (k+j+1) else 0)^2 ≤
      traceExtraRadius (k+j+1)^2/((m:ℝ)+1)^2 := by
    split_ifs with h
    · simp only [traceBalloonRadius,h,lt_self_iff_false,ite_false,div_pow,le_refl]
    · simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      positivity
  have hleft : Summable (fun k : ℕ =>
      (if r (k+j+1) = 0 then traceBalloonRadius r m (k+j+1) else 0)^2) :=
    hs.of_nonneg_of_le (fun _ => sq_nonneg _) hp
  apply (hleft.tsum_le_tsum hp hs).trans
  rw [tsum_div_const,traceExtraRadius_tail]
  simp only [traceBalloonRadius,hrj,lt_self_iff_false,ite_false,div_pow]
  have hnon : 0 ≤ traceExtraRadius j^2/((m:ℝ)+1)^2 := by positivity
  have he : traceExtraRadius j^2/3/((m:ℝ)+1)^2 =
      (traceExtraRadius j^2/((m:ℝ)+1)^2)/3 := by ring
  rw [he]
  nlinarith

end CircleDomainRigidity

end

end OAI
