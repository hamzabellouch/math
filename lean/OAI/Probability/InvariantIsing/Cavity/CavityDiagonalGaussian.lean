import OAI.Probability.InvariantIsing.Cavity.CavityGaussianIntegral

namespace OAI

/-! Independent-coordinate quadratic Gaussian integrals, allowing
singular diagonal covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

theorem cavity_diagonal_gaussian_integrable {d : ℕ}
    (v : Fin d → ℝ≥0) (a u : Fin d → ℝ)
    (hq : ∀ i, 0 < 1 - v i * a i) :
    Integrable (fun z : Fin d → ℝ =>
      Real.exp (∑ i, a i / 2 * (u i + z i) ^ 2))
      (Measure.pi fun i => gaussianReal 0 (v i)) := by
  simp_rw [Real.exp_sum]
  exact Integrable.fintype_prod (fun i =>
    cavity_gaussian_quadratic_integrable (v i) (a i) (u i) (hq i))

theorem cavity_diagonal_gaussian_integral {d : ℕ}
    (v : Fin d → ℝ≥0) (a u : Fin d → ℝ)
    (hq : ∀ i, 0 < 1 - v i * a i) :
    (∫ z : Fin d → ℝ, Real.exp (∑ i, a i / 2 * (u i + z i) ^ 2)
      ∂Measure.pi (fun i => gaussianReal 0 (v i))) =
      (∏ i, (Real.sqrt (1 - v i * a i))⁻¹) *
        Real.exp (∑ i, a i * u i ^ 2 / (2 * (1 - v i * a i))) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (a i / 2 * (u i + x) ^ 2))]
  simp_rw [cavity_gaussian_quadratic_integral _ _ _ (hq _)]
  exact Finset.prod_mul_distrib

theorem cavity_diagonal_gaussian_logIntegral {d : ℕ}
    (v : Fin d → ℝ≥0) (a u : Fin d → ℝ)
    (hq : ∀ i, 0 < 1 - v i * a i) :
    Real.log (∫ z : Fin d → ℝ, Real.exp (∑ i, a i / 2 * (u i + z i) ^ 2)
      ∂Measure.pi (fun i => gaussianReal 0 (v i))) =
      -(∑ i, Real.log (1 - v i * a i)) / 2 +
        ∑ i, a i * u i ^ 2 / (2 * (1 - v i * a i)) := by
  have hpos : ∀ i, 0 < (Real.sqrt (1 - v i * a i))⁻¹ := by
    intro i
    exact inv_pos.mpr (Real.sqrt_pos.2 (hq i))
  rw [cavity_diagonal_gaussian_integral v a u hq,
    Real.log_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => (hpos i).ne'))
      (Real.exp_ne_zero _), Real.log_exp, Real.log_prod]
  · simp_rw [Real.log_inv, Real.log_sqrt (hq _).le]
    rw [Finset.sum_neg_distrib, ← Finset.sum_div]
    ring
  · intro i _
    exact (hpos i).ne'

end InvariantIsing

end

end OAI
