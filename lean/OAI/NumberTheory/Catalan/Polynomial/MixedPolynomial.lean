import OAI.NumberTheory.Catalan.Analysis.MixedSeries

namespace OAI

noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem mixedPolynomial_kernel_eq (P Q : ℝ[X]) (t s : ℝ) :
    (|t| / Real.sqrt (1 - t ^ 2)) * (P.eval t * Q.eval s) / (1 - t * s) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) *
          ((|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem integrable_mixedPolynomial (P Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ => (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (P.eval p.1 * Q.eval p.2) / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  simp_rw [mixedPolynomial_kernel_eq]
  exact integrable_finsetSum P.support fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_mixedKernel i j).const_mul (P.coeff i * Q.coeff j)

theorem integral_prod_mixedPolynomial (P Q : ℝ[X]) :
    (∫ p : ℝ × ℝ, (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (P.eval p.1 * Q.eval p.2) / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * mixedMoment (X ^ i) (X ^ j) := by
  simp_rw [mixedPolynomial_kernel_eq]
  rw [integral_finsetSum P.support (fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_mixedKernel i j).const_mul (P.coeff i * Q.coeff j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Q.support (fun j _ =>
    (integrable_mixedKernel i j).const_mul (P.coeff i * Q.coeff j))]
  simp only [MeasureTheory.integral_const_mul, mixedMoment_X_pow_eq_integral_prod]

theorem mixedMoment_eq_sum (P Q : ℝ[X]) :
    mixedMoment P Q = ∑ i ∈ P.support, ∑ j ∈ Q.support,
      (P.coeff i * Q.coeff j) * mixedMoment (X ^ i) (X ^ j) := by
  have h := integral_prod
    (fun p : ℝ × ℝ => (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (P.eval p.1 * Q.eval p.2) / (1 - p.1 * p.2))
    (integrable_mixedPolynomial P Q)
  rw [integral_prod_mixedPolynomial] at h
  simpa only [mixedMoment,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm

end InternalCatalan

end

end OAI
