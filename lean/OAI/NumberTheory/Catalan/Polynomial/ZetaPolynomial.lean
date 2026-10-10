import OAI.NumberTheory.Catalan.Energy.ZetaOffDiagonal

namespace OAI

noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem zetaPolynomial_kernel_eq (P Q : ℝ[X]) (t s : ℝ) :
    P.eval t * Q.eval s / (1 - t * s) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * (t ^ i * s ^ j / (1 - t * s)) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem integrable_zetaPolynomial (P Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ => P.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  simp_rw [zetaPolynomial_kernel_eq]
  exact integrable_finsetSum P.support fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_zetaKernel i j).const_mul (P.coeff i * Q.coeff j)

theorem integral_prod_zetaPolynomial (P Q : ℝ[X]) :
    (∫ p : ℝ × ℝ, P.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * zetaSeries i j := by
  simp_rw [zetaPolynomial_kernel_eq]
  rw [integral_finsetSum P.support (fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_zetaKernel i j).const_mul (P.coeff i * Q.coeff j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Q.support (fun j _ =>
    (integrable_zetaKernel i j).const_mul (P.coeff i * Q.coeff j))]
  simp only [MeasureTheory.integral_const_mul, integral_prod_zetaKernel]

theorem zetaMoment_eq_sum (P Q : ℝ[X]) :
    zetaMoment P Q = ∑ i ∈ P.support, ∑ j ∈ Q.support,
      (P.coeff i * Q.coeff j) * zetaSeries i j := by
  have h := integral_prod
    (fun p : ℝ × ℝ => P.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2))
    (integrable_zetaPolynomial P Q)
  rw [integral_prod_zetaPolynomial] at h
  simpa only [zetaMoment,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm

theorem zetaMoment_X_pow_decomposition (i j : ℕ) :
    zetaMoment (X ^ i) (X ^ j) = (zetaRat i j : ℝ) +
      if i = j then zetaSeries 0 0 else 0 := by
  rw [zetaMoment_X_pow, zetaSeries_eq_zetaRat_add]

theorem zetaMoment_decomposition (P Q : ℝ[X]) :
    zetaMoment P Q =
      (∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * (zetaRat i j : ℝ)) +
      (∑ i ∈ P.support, P.coeff i * Q.coeff i) * zetaSeries 0 0 := by
  have hexp : zetaMoment P Q =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) *
          ((zetaRat i j : ℝ) + if i = j then zetaSeries 0 0 else 0) := by
    rw [zetaMoment_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun x : ℝ => (P.coeff i * Q.coeff j) * x)
      (zetaSeries_eq_zetaRat_add i j)
  rw [hexp]
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Ne.symm hji]
  · intro hnot
    have hzero : Q.coeff i = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using hnot
    simp [hzero]

end InternalCatalan

end

end OAI
