import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticAlgebra

namespace OAI

/-! Scalar square completion for the quadratic cavity tilt.  The variance
may vanish; only positivity of the resulting precision is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

private lemma cavity_complete_square (b c d x : ℝ) (hb : b ≠ 0) :
    -b * x ^ 2 + c * x + d =
      -b * (x - c / (2 * b)) ^ 2 + (c ^ 2 / (4 * b) + d) := by
  field_simp [hb]
  ring

lemma cavity_integrable_exp_quadratic (b c d : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-b * x ^ 2 + c * x + d)) := by
  have h := ((integrable_exp_neg_mul_sq hb).comp_sub_right (c / (2 * b))).mul_const
    (Real.exp (c ^ 2 / (4 * b) + d))
  convert h using 1
  funext x
  rw [← Real.exp_add, cavity_complete_square b c d x hb.ne']

lemma cavity_integral_exp_quadratic (b c d : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-b * x ^ 2 + c * x + d)) =
      Real.sqrt (Real.pi / b) * Real.exp (c ^ 2 / (4 * b) + d) := by
  simp_rw [cavity_complete_square b c d _ hb.ne', Real.exp_add]
  rw [integral_mul_const, integral_sub_right_eq_self
    (fun x : ℝ => Real.exp (-b * x ^ 2)) (c / (2 * b)), integral_gaussian]

private lemma cavity_gaussian_weighted_integrand (v : ℝ≥0) (a u z : ℝ) :
    gaussianPDFReal 0 v z * Real.exp (a / 2 * (u + z) ^ 2) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ *
        Real.exp (-( (1 - v * a) / (2 * v)) * z ^ 2 +
          (a * u) * z + a * u ^ 2 / 2) := by
  by_cases hv : (v : ℝ) = 0
  · simp [gaussianPDFReal, hv]
  simp only [gaussianPDFReal, sub_zero, mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  field_simp [hv]
  ring

private lemma cavity_gaussian_normalizer (v : ℝ≥0) (a : ℝ)
    (hv : 0 < (v : ℝ)) (hq : 0 < 1 - v * a) :
    (Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.sqrt (Real.pi / ((1 - v * a) / (2 * v))) =
      (Real.sqrt (1 - v * a))⁻¹ := by
  calc
    _ = Real.sqrt ((Real.pi / ((1 - v * a) / (2 * v))) /
        (2 * Real.pi * v)) := by
      conv_rhs => rw [Real.sqrt_div' _ (by positivity)]
      ring
    _ = Real.sqrt ((1 - v * a)⁻¹) := by
      congr 1
      field_simp [hv.ne', hq.ne', Real.pi_ne_zero]
    _ = _ := Real.sqrt_inv _

private lemma cavity_gaussian_constant (v a u : ℝ)
    (hq : 1 - v * a ≠ 0) :
    (a * u) ^ 2 / (4 * ((1 - v * a) / (2 * v))) + a * u ^ 2 / 2 =
      a * u ^ 2 / (2 * (1 - v * a)) := by
  have hq' : 1 - a * v ≠ 0 := by simpa only [mul_comm] using hq
  field_simp [hq, hq']
  ring

/-- Exponential integrability includes the degenerate Gaussian. -/
theorem cavity_gaussian_quadratic_integrable (v : ℝ≥0) (a u : ℝ)
    (hq : 0 < 1 - v * a) :
    Integrable (fun z : ℝ => Real.exp (a / 2 * (u + z) ^ 2)) (gaussianReal 0 v) := by
  by_cases hv : v = 0
  · rw [hv, gaussianReal_zero_var]
    exact integrable_dirac (by simp)
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hb : 0 < (1 - (v : ℝ) * a) / (2 * v) := by positivity
  rw [gaussianReal_of_var_ne_zero 0 hv]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
    (ae_of_all _ (fun _ => gaussianPDF_lt_top))).2
  simp only [toReal_gaussianPDF, smul_eq_mul]
  simp_rw [cavity_gaussian_weighted_integrand]
  exact (cavity_integrable_exp_quadratic _ _ _ hb).const_mul _

/-- The one-dimensional form of `cav:q-gaussian-integral`, including
singular covariance `v = 0`. -/
theorem cavity_gaussian_quadratic_integral (v : ℝ≥0) (a u : ℝ)
    (hq : 0 < 1 - v * a) :
    (∫ z : ℝ, Real.exp (a / 2 * (u + z) ^ 2) ∂gaussianReal 0 v) =
      (Real.sqrt (1 - v * a))⁻¹ * Real.exp (a * u ^ 2 / (2 * (1 - v * a))) := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
    ring
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hb : 0 < (1 - (v : ℝ) * a) / (2 * v) := by positivity
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  simp_rw [cavity_gaussian_weighted_integrand]
  rw [integral_const_mul, cavity_integral_exp_quadratic _ _ _ hb]
  rw [← mul_assoc, cavity_gaussian_normalizer v a hvpos hq,
    cavity_gaussian_constant v a u hq.ne']

theorem cavity_gaussian_quadratic_logIntegral (v : ℝ≥0) (a u : ℝ)
    (hq : 0 < 1 - v * a) :
    Real.log (∫ z : ℝ, Real.exp (a / 2 * (u + z) ^ 2) ∂gaussianReal 0 v) =
      -(Real.log (1 - v * a)) / 2 + a * u ^ 2 / (2 * (1 - v * a)) := by
  rw [cavity_gaussian_quadratic_integral v a u hq,
    Real.log_mul (inv_ne_zero (Real.sqrt_ne_zero'.mpr hq)) (Real.exp_ne_zero _),
    Real.log_inv, Real.log_sqrt hq.le, Real.log_exp]
  ring

end InvariantIsing

end

end OAI
