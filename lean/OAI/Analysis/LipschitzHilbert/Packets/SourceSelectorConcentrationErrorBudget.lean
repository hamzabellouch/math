import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorMoments
import OAI.Analysis.LipschitzHilbert.Estimates.TopThreshold

namespace OAI

/-! The weighted error moment constant costs only a fixed polynomial.
All thresholds are chosen before the packet family and geometric scales. -/

noncomputable section
namespace LipschitzHilbert

theorem selectorErrorMomentBase_affine (B : ℝ) :
    selectorErrorMomentBase B = selectorErrorMomentBase 0+
      (selectorErrorMomentBase 1-selectorErrorMomentBase 0)*B := by
  unfold selectorErrorMomentBase
  ring

theorem selectorErrorMomentBase_slope_nonneg :
    0 ≤ selectorErrorMomentBase 1-selectorErrorMomentBase 0 := by
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have heq : selectorErrorMomentBase 1-selectorErrorMomentBase 0 =
      16*((4*(2*(1024*Real.pi^2)+240*Real.pi))/Real.log (3/2)+1024*Real.pi^2) := by
    unfold selectorErrorMomentBase
    ring
  rw [heq]
  positivity

theorem selectorErrorMomentBase_le_power {B L p : ℝ} (hL : 1 ≤ L)
    (hp : 0 ≤ p) (hB : B ≤ L^p) :
    selectorErrorMomentBase B ≤ selectorErrorMomentBase 1*L^p := by
  have hLp : 1 ≤ L^p := Real.one_le_rpow hL hp
  rw [selectorErrorMomentBase_affine B]
  have h0 := selectorErrorMomentBase_pos (B := 0) (by norm_num)
  have hs := selectorErrorMomentBase_slope_nonneg
  calc
    _ ≤ selectorErrorMomentBase 0*L^p+
        (selectorErrorMomentBase 1-selectorErrorMomentBase 0)*L^p :=
      add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left hB hs)
    _ = _ := by ring

theorem exists_selector_error_top_threshold (J a p : ℝ) (D : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ C B : ℝ,
      0 ≤ C → 0 ≤ B → C ≤ L^p → B ≤ L^(p+4) →
      256^(8*D+1)*(16*topPairConstant C (8*D+1)*selectorErrorMomentBase B)*
        (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ)*5^(8*D) ≤ L^(2*p+6) := by
  let m : ℝ := (J+Real.log (topAreaPrefactor 1)+2*a)/Real.log 4+2
  let A : ℝ := 256^(8*D+1)*(16*topPairConstant 1 (8*D+1)*selectorErrorMomentBase 1)*m*5^(8*D)
  have hm : 0 < m := by
    have hlog := Real.log_nonneg topAreaPrefactor_one_le
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp [m]
    positivity
  have hA : 0 < A := by
    have ht := topPairConstant_pos 1 (8*D+1) (by norm_num)
    have he := selectorErrorMomentBase_pos (B := 1) (by norm_num)
    dsimp [A]
    positivity
  refine ⟨max 1 A,le_max_left _ _,?_⟩
  intro L hLL C B _hC hB0 hCb hB
  have hL : 1 ≤ L := (le_max_left _ _).trans hLL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hAL : A ≤ L := (le_max_right _ _).trans hLL
  have htop : topPairConstant C (8*D+1) = topPairConstant 1 (8*D+1)*C := by
    unfold topPairConstant
    ring
  have he := selectorErrorMomentBase_le_power hL (by linarith : 0 ≤ p+4) hB
  have hn := topExceptionMoment_power_le J a L hJ ha hL
  change (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ) ≤ m*L at hn
  have htpos := topPairConstant_pos 1 (8*D+1) (by norm_num)
  have hepos := selectorErrorMomentBase_pos (B := 1) (by norm_num)
  have hCmul : 16*(topPairConstant 1 (8*D+1)*C) ≤
      16*topPairConstant 1 (8*D+1)*L^p := by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hCb (show 0 ≤ 16*topPairConstant 1 (8*D+1) by positivity)
  have hcoeff : 256^(8*D+1)*(16*topPairConstant C (8*D+1)*selectorErrorMomentBase B) ≤
      256^(8*D+1)*(16*topPairConstant 1 (8*D+1)*L^p*
        (selectorErrorMomentBase 1*L^(p+4))) := by
    rw [htop]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul hCmul he
      (selectorErrorMomentBase_pos hB0).le
      (by positivity)
  calc
    _ ≤ (256^(8*D+1)*(16*topPairConstant 1 (8*D+1)*L^p*
        (selectorErrorMomentBase 1*L^(p+4))))*(m*L)*5^(8*D) := by
      have hleft := mul_le_mul hcoeff hn (Nat.cast_nonneg _)
        (by positivity : 0 ≤ 256^(8*D+1)*(16*topPairConstant 1 (8*D+1)*L^p*
          (selectorErrorMomentBase 1*L^(p+4))))
      exact mul_le_mul_of_nonneg_right hleft (by positivity)
    _ = A*L^(2*p+5) := by
      have hpowers : L^p*L^(p+4)*L = L^(2*p+5) := by
        calc
          _ = L^(p+(p+4))*L^1 := by rw [Real.rpow_add hL0 p (p+4),Real.rpow_one]
          _ = L^((p+(p+4))+1) := (Real.rpow_add hL0 _ _).symm
          _ = _ := by congr 1; ring
      calc
        _ = A*(L^p*L^(p+4)*L) := by dsimp [A]; ring
        _ = _ := by rw [hpowers]
    _ ≤ L*L^(2*p+5) := mul_le_mul_of_nonneg_right hAL (Real.rpow_nonneg hL0.le _)
    _ = L^(2*p+6) := by
      calc
        _ = L^1*L^(2*p+5) := by rw [Real.rpow_one]
        _ = L^(1+(2*p+5)) := (Real.rpow_add hL0 _ _).symm
        _ = _ := by congr 1; ring

end LipschitzHilbert

end

end OAI
