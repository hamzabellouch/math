import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteGaussian
import Mathlib.Probability.Moments.Variance

namespace OAI

/-!
# Second moments of the complex Fourier coefficients

The complex Gaussian used for finite Fourier blocks has second moment twice
the variance of one real coordinate. This includes the zero-variance case.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DefocusingNLS

/-- The nonnegative second moment of a centered real Gaussian. -/
theorem real_gaussian_second_moment (v : ℝ≥0) :
    (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂gaussianReal 0 v) = v := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := v) 2).ofReal_variance_eq
  rw [evariance_eq_lintegral_ofReal] at h
  simpa using h.symm

/-- A complex coefficient with independent real/imaginary variance `v` has
squared-modulus expectation `2*v`. -/
theorem complex_gaussian_second_moment (v : ℝ≥0) :
    (∫⁻ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) ∂complexGaussian v) = 2 * v := by
  rw [complexGaussian, lintegral_map (by fun_prop) (by fun_prop)]
  have hnorm (p : ℝ × ℝ) :
      ‖Complex.equivRealProdCLM.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.equivRealProdCLM_symm_apply, pow_two]
  simp_rw [hnorm, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  rw [lintegral_add_left (by fun_prop)]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  simp [real_gaussian_second_moment, two_mul]

/-- The standard complex Gaussian has unit squared-modulus expectation. -/
theorem standard_complex_gaussian_normSq_moment :
    (∫⁻ z : ℂ, ENNReal.ofReal (Complex.normSq z) ∂complexGaussian (1 / 2)) = 1 := by
  have h := complex_gaussian_second_moment (1 / 2)
  norm_num [Complex.normSq_eq_norm_sq] at h ⊢
  exact h.trans (ENNReal.mul_inv_cancel (by norm_num) (by simp))

end DefocusingNLS

end OAI
