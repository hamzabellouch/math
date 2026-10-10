import OAI.Probability.SLE.Angle.AnglePolynomialCoefficients

namespace OAI

/-! Monic polynomial eigenfunctions for the centered cosine generator.
The coefficients are solved downwards in degree, with no choice of an
auxiliary stochastic process or additional published input. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

def angleEigenCoefficient (κ : ℝ) (N k : ℕ) : ℝ :=
  if k=N then 1 else if _h : k<N then
    ((κ/8)*((k:ℝ)+2)*((k:ℝ)+1)/(anglePolynomialEigenvalue κ k-anglePolynomialEigenvalue κ N))*
      angleEigenCoefficient κ N (k+2)
  else 0
termination_by N-k
  decreasing_by omega

lemma angleEigenCoefficient_top (κ : ℝ) (N : ℕ) : angleEigenCoefficient κ N N=1 := by
  rw [angleEigenCoefficient,ite_eq_left rfl]

lemma angleEigenCoefficient_above (κ : ℝ) {N k : ℕ} (h : N<k) :
    angleEigenCoefficient κ N k=0 := by
  rw [angleEigenCoefficient,ite_eq_right (ne_of_gt h),dite_eq_right (by omega)]

lemma angleEigenCoefficient_recurrence {κ : ℝ} (hκ : 0<κ) (N k : ℕ) :
    (κ/8)*((k:ℝ)+2)*((k:ℝ)+1)*angleEigenCoefficient κ N (k+2) =
      (anglePolynomialEigenvalue κ k-anglePolynomialEigenvalue κ N)*angleEigenCoefficient κ N k := by
  rcases lt_trichotomy k N with hk | heq | hk
  · have he : anglePolynomialEigenvalue κ k-anglePolynomialEigenvalue κ N ≠ 0 :=
      sub_ne_zero.mpr (ne_of_lt (anglePolynomialEigenvalue_strictMono hκ hk))
    conv_rhs => rw [angleEigenCoefficient]
    rw [ite_eq_right (ne_of_lt hk),dite_eq_left hk]
    field_simp
  · subst k
    rw [angleEigenCoefficient_above κ (by omega : N<N+2),angleEigenCoefficient_top]
    ring
  · rw [angleEigenCoefficient_above κ (by omega : N<k+2),angleEigenCoefficient_above κ hk]
    ring

def angleEigenPolynomial (κ : ℝ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (N+1), monomial k (angleEigenCoefficient κ N k)

lemma angleEigenPolynomial_coeff (κ : ℝ) (N k : ℕ) :
    (angleEigenPolynomial κ N).coeff k=angleEigenCoefficient κ N k := by
  by_cases hk : k<N+1
  · simp [angleEigenPolynomial,coeff_monomial,Finset.sum_ite_eq',hk]
  · simp [angleEigenPolynomial,coeff_monomial,Finset.sum_ite_eq',hk,
      angleEigenCoefficient_above κ (by omega : N<k)]

lemma angleEigenPolynomial_natDegree_le (κ : ℝ) (N : ℕ) :
    (angleEigenPolynomial κ N).natDegree ≤ N := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [angleEigenPolynomial_coeff,angleEigenCoefficient_above κ hk]

lemma angleEigenPolynomial_monic (κ : ℝ) (N : ℕ) : (angleEigenPolynomial κ N).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one N (angleEigenPolynomial_natDegree_le κ N)
  rw [angleEigenPolynomial_coeff,angleEigenCoefficient_top]

lemma angleEigenPolynomial_natDegree (κ : ℝ) (N : ℕ) : (angleEigenPolynomial κ N).natDegree=N := by
  apply le_antisymm (angleEigenPolynomial_natDegree_le κ N)
  apply le_natDegree_of_ne_zero
  rw [angleEigenPolynomial_coeff,angleEigenCoefficient_top]
  norm_num

lemma angleEigenPolynomial_eigen {κ : ℝ} (hκ : 0<κ) (N : ℕ) :
    anglePolynomialGenerator κ (angleEigenPolynomial κ N) =
      -C (anglePolynomialEigenvalue κ N)*angleEigenPolynomial κ N := by
  apply (anglePolynomial_eigen_iff_coeff κ _ N).mpr
  intro k
  simp only [angleEigenPolynomial_coeff]
  exact angleEigenCoefficient_recurrence hκ N k

end SLEExactGauge

end

end OAI
