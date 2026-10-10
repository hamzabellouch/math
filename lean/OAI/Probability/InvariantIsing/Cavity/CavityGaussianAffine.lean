import OAI.Probability.InvariantIsing.Cavity.CavityDiagonalGaussian

namespace OAI

/-! Affine quadratic Gaussian integrals.  Independent linear terms are
needed after diagonalizing the precision of a noncommuting cavity tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

private lemma cavity_affine_complete_square (a c d z : ℝ) (ha : a ≠ 0) :
    Real.exp (a / 2 * z ^ 2 + c * z + d) =
      Real.exp (a / 2 * (c / a + z) ^ 2) * Real.exp (d - c ^ 2 / (2 * a)) := by
  rw [← Real.exp_add]
  congr 1
  field_simp [ha]
  ring

private lemma cavity_affine_constant (v a c d : ℝ) (ha : a ≠ 0)
    (hq : 1 - v * a ≠ 0) :
    a * (c / a) ^ 2 / (2 * (1 - v * a)) + (d - c ^ 2 / (2 * a)) =
      d + v * c ^ 2 / (2 * (1 - v * a)) := by
  have hq' : 1 - a * v ≠ 0 := by simpa only [mul_comm] using hq
  field_simp [ha, hq, hq']
  ring

private lemma cavity_gaussian_linear_integral (v : ℝ≥0) (c : ℝ) :
    (∫ z : ℝ, Real.exp (c * z) ∂gaussianReal 0 v) =
      Real.exp (v * c ^ 2 / 2) := by
  simpa only [mgf, zero_mul, zero_add] using
    congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) c

theorem cavity_gaussian_affine_integrable (v : ℝ≥0) (a c d : ℝ)
    (hq : 0 < 1 - v * a) :
    Integrable (fun z : ℝ => Real.exp (a / 2 * z ^ 2 + c * z + d))
      (gaussianReal 0 v) := by
  by_cases ha : a = 0
  · simpa only [ha, zero_div, zero_mul, zero_add, Real.exp_add] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := v) c).mul_const (Real.exp d)
  simp_rw [cavity_affine_complete_square a c d _ ha]
  exact (cavity_gaussian_quadratic_integrable v a (c / a) hq).mul_const _

theorem cavity_gaussian_affine_integral (v : ℝ≥0) (a c d : ℝ)
    (hq : 0 < 1 - v * a) :
    (∫ z : ℝ, Real.exp (a / 2 * z ^ 2 + c * z + d) ∂gaussianReal 0 v) =
      (Real.sqrt (1 - v * a))⁻¹ *
        Real.exp (d + v * c ^ 2 / (2 * (1 - v * a))) := by
  by_cases ha : a = 0
  · simp only [ha, zero_div, zero_mul, zero_add, mul_zero, sub_zero,
      Real.sqrt_one, inv_one, one_mul, mul_one, Real.exp_add, integral_mul_const]
    rw [cavity_gaussian_linear_integral]
    ring
  simp_rw [cavity_affine_complete_square a c d _ ha]
  rw [integral_mul_const, cavity_gaussian_quadratic_integral v a (c / a) hq,
    mul_assoc, ← Real.exp_add, cavity_affine_constant v a c d ha hq.ne']

theorem cavity_gaussian_affine_logIntegral (v : ℝ≥0) (a c d : ℝ)
    (hq : 0 < 1 - v * a) :
    Real.log (∫ z : ℝ, Real.exp (a / 2 * z ^ 2 + c * z + d) ∂gaussianReal 0 v) =
      -(Real.log (1 - v * a)) / 2 + d + v * c ^ 2 / (2 * (1 - v * a)) := by
  rw [cavity_gaussian_affine_integral v a c d hq,
    Real.log_mul (inv_ne_zero (Real.sqrt_ne_zero'.mpr hq)) (Real.exp_ne_zero _),
    Real.log_inv, Real.log_sqrt hq.le, Real.log_exp]
  ring

theorem cavity_diagonal_gaussian_affine_integrable {d : ℕ}
    (v : Fin d → ℝ≥0) (a c : Fin d → ℝ)
    (hq : ∀ i, 0 < 1 - v i * a i) :
    Integrable (fun z : Fin d → ℝ =>
      Real.exp (∑ i, (a i / 2 * z i ^ 2 + c i * z i)))
      (Measure.pi fun i => gaussianReal 0 (v i)) := by
  simp_rw [Real.exp_sum]
  apply Integrable.fintype_prod (f := fun i z => Real.exp (a i / 2 * z ^ 2 + c i * z))
  intro i
  simpa only [add_zero] using cavity_gaussian_affine_integrable (v i) (a i) (c i) 0 (hq i)

theorem cavity_diagonal_gaussian_affine_integral {d : ℕ}
    (v : Fin d → ℝ≥0) (a c : Fin d → ℝ)
    (hq : ∀ i, 0 < 1 - v i * a i) :
    (∫ z : Fin d → ℝ, Real.exp (∑ i, (a i / 2 * z i ^ 2 + c i * z i))
      ∂Measure.pi (fun i => gaussianReal 0 (v i))) =
      (∏ i, (Real.sqrt (1 - v i * a i))⁻¹) *
        Real.exp (∑ i, v i * c i ^ 2 / (2 * (1 - v i * a i))) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (fun i x => Real.exp (a i / 2 * x ^ 2 + c i * x))]
  have hi i := cavity_gaussian_affine_integral (v i) (a i) (c i) 0 (hq i)
  simp only [add_zero, zero_add] at hi
  simp_rw [hi]
  exact Finset.prod_mul_distrib

end InvariantIsing

end

end OAI
