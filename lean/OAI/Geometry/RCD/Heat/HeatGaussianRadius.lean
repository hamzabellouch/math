import OAI.Geometry.RCD.Heat.HeatPointEvaluation

namespace OAI

/-! # A common radius below the time and curvature scales -/

noncomputable section
namespace RegularPointCoordinates

def gaussianRadius (K t : ℝ) : ℝ :=
  Real.sqrt t/(2*(1+Real.sqrt (|K| *t)))

theorem gaussianRadius_pos (K : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < gaussianRadius K t := by
  dsimp only [gaussianRadius]
  positivity

theorem gaussianRadius_le (K : ℝ) {t : ℝ} (_ht : 0 < t) :
    gaussianRadius K t ≤ Real.sqrt t/2 := by
  dsimp only [gaussianRadius]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg t) (by norm_num)
    (by nlinarith only [Real.sqrt_nonneg (|K| *t)])

theorem gaussianRadius_sq_lt (K : ℝ) {t : ℝ} (ht : 0 < t) :
    (gaussianRadius K t)^2 < t/2 := by
  have h := gaussianRadius_le K ht
  have hr := gaussianRadius_pos K ht
  have hs := Real.sq_sqrt ht.le
  nlinarith only [h,hr,hs,Real.sqrt_nonneg t]

theorem gaussianRadius_curvature (K : ℝ) {t : ℝ} (ht : 0 < t) :
    -1 ≤ K*(gaussianRadius K t)^2 := by
  have hs := Real.sq_sqrt (mul_nonneg (abs_nonneg K) ht.le)
  have hnonneg := Real.sqrt_nonneg (|K| *t)
  have hden : 0 < 2*(1+Real.sqrt (|K| *t)) := by positivity
  have hfrac : |K| *(gaussianRadius K t)^2 ≤ 1 := by
    dsimp only [gaussianRadius]
    rw [div_pow,Real.sq_sqrt ht.le,← mul_div_assoc]
    apply (div_le_one (sq_pos_of_pos hden)).mpr
    nlinarith only [hs,hnonneg]
  have hk := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (gaussianRadius K t))
  nlinarith only [hfrac,hk]

end RegularPointCoordinates

end

end OAI
