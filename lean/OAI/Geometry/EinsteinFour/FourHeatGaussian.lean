import OAI.Geometry.Manifold.ProjectiveSphere
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

/-! The normalized Euclidean four-dimensional Gaussian used in the local
heat construction. All integrals use the actual Euclidean volume measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory GaussianFourier

noncomputable section

def fourHeatGaussian (t : ℝ) (x : FourSpace) : ℝ :=
  ((4 * Real.pi * t) ^ 2)⁻¹ * Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2)

theorem fourHeatGaussian_pos (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    0 < fourHeatGaussian t x := by
  unfold fourHeatGaussian
  positivity

theorem fourHeatGaussian_continuous (t : ℝ) : Continuous (fourHeatGaussian t) := by
  exact continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_norm.pow 2)))

theorem fourGaussian_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : FourSpace => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (integrable_cexp_neg_mul_sq_norm_add (V := FourSpace) (b := (b : ℂ))
    (by simpa using hb) 0 0).re
  convert h using 1
  funext x
  simp only [zero_mul, add_zero]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp]
  rfl

theorem fourHeatGaussian_integrable (t : ℝ) (ht : 0 < t) : Integrable (fourHeatGaussian t) :=
  (fourGaussian_integrable (4 * t)⁻¹ (by positivity)).const_mul _

theorem fourHeatGaussian_mass (t : ℝ) (ht : 0 < t) :
    (∫ x : FourSpace, fourHeatGaussian t x) = 1 := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  have hg := integral_rexp_neg_mul_sq_norm (V := FourSpace) hb
  have hd : Module.finrank ℝ FourSpace = 4 := by simp [FourSpace]
  have hd2 : (Module.finrank ℝ FourSpace : ℝ) / 2 = 2 := by norm_num [hd]
  rw [hd2, Real.rpow_two] at hg
  simp only [fourHeatGaussian]
  rw [integral_const_mul, hg]
  have ht0 := ne_of_gt ht
  field_simp [Real.pi_ne_zero, ht0]

end
end PositiveEinsteinFour.Geometry

end OAI
