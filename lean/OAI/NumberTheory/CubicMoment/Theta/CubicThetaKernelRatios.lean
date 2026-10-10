import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNormalizedJets
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKernelEquation

namespace OAI

/-! Uniform coordinate ratios for differentiating the hyperbolic
kernel on a region with positive lower height. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCartesian_radius_pos (x y : ℝ) {v : ℝ} (hv : 0<v) :
    0<x^2+y^2+v^2 := by
  nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]

lemma cubicTheta_horizontal_ratio (x y : ℝ) {v : ℝ} (hv : 0<v) :
    |x|/(x^2+y^2+v^2) ≤ 1/v := by
  apply (div_le_div_iff₀ (cubicThetaCartesian_radius_pos x y hv) hv).mpr
  nlinarith [sq_abs x,sq_nonneg (v-|x|),sq_nonneg y]

lemma cubicTheta_vertical_ratio (x y : ℝ) {v : ℝ} (hv : 0<v) :
    v/(x^2+y^2+v^2) ≤ 1/v := by
  apply (div_le_div_iff₀ (cubicThetaCartesian_radius_pos x y hv) hv).mpr
  nlinarith [sq_nonneg x,sq_nonneg y]

lemma cubicTheta_radius_inverse (x y : ℝ) {v : ℝ} (hv : 0<v) :
    1/(x^2+y^2+v^2) ≤ 1/v^2 :=
  one_div_le_one_div_of_le (sq_pos_of_pos hv) (by nlinarith [sq_nonneg x,sq_nonneg y])

lemma cubicTheta_horizontal_square_ratio (x y : ℝ) {v : ℝ} (hv : 0<v) :
    x^2/(x^2+y^2+v^2)^2 ≤ 1/v^2 := by
  have h := (sq_le_sq₀ (div_nonneg (abs_nonneg x) (cubicThetaCartesian_radius_pos x y hv).le)
    (one_div_pos.mpr hv).le).mpr (cubicTheta_horizontal_ratio x y hv)
  simpa only [div_pow,sq_abs,one_pow] using h

lemma cubicTheta_vertical_square_ratio (x y : ℝ) {v : ℝ} (hv : 0<v) :
    v^2/(x^2+y^2+v^2)^2 ≤ 1/v^2 := by
  have h := (sq_le_sq₀ (div_nonneg hv.le (cubicThetaCartesian_radius_pos x y hv).le)
    (one_div_pos.mpr hv).le).mpr (cubicTheta_vertical_ratio x y hv)
  simpa only [div_pow,one_pow] using h

end CubicFirstMoment

end

end OAI
