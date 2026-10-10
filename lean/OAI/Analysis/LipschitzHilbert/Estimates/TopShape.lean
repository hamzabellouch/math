import OAI.Analysis.LipschitzHilbert.Estimates.TopMaskApproximation

namespace OAI

/-! The exact top shape from (src-5) and its seventh-power decay
outside the mask's near region. -/

noncomputable section

namespace LipschitzHilbert

def topShape (K D x y : ℝ) : ℝ :=
  (2:ℝ)^D*(1+(|x|+|y|)/K)^(-D)

theorem topShape_nonneg (K D x y : ℝ) (hK : 0 < K) : 0 ≤ topShape K D x y := by
  unfold topShape
  positivity

theorem topShape_le (K D x y : ℝ) (hK : 0 < K) (hD : 0 ≤ D) :
    topShape K D x y ≤ (2:ℝ)^D := by
  have hb : 1 ≤ 1+(|x|+|y|)/K := le_add_of_nonneg_right
    (div_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y)) hK.le)
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hD)
  exact (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num) D)).trans_eq (mul_one _)

theorem topShape_far_seventh (L A A1 D x y : ℝ) (hL : 0 < L) (hD : 0 ≤ D)
    (hfar : ¬ (|x| ≤ L^(A/2) ∧ |y| ≤ L^(A/2))) :
    (topShape (L^A1) D x y)^7 ≤
      ((2:ℝ)^D)^7*L^(-7*D*(A/2-A1)) := by
  have hK : 0 < L^A1 := Real.rpow_pos_of_pos hL _
  have hdist : L^(A/2) ≤ |x|+|y| := by
    by_contra h
    apply hfar
    constructor <;> linarith [abs_nonneg x, abs_nonneg y]
  have hbase : L^(A/2-A1) ≤ 1+(|x|+|y|)/(L^A1) := by
    rw [Real.rpow_sub hL]
    have h := div_le_div_of_nonneg_right hdist hK.le
    linarith
  have hb : 0 ≤ 1+(|x|+|y|)/(L^A1) := by positivity
  have heq : (topShape (L^A1) D x y)^7 =
      ((2:ℝ)^D)^7*(1+(|x|+|y|)/(L^A1))^(-7*D) := by
    unfold topShape
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
    congr 1
    ring
  rw [heq]
  have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hL (A/2-A1)) hbase
    (show -7*D ≤ 0 by linarith)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  convert hp using 1
  rw [← Real.rpow_mul hL.le]
  congr 1
  ring

end LipschitzHilbert

end

end OAI
