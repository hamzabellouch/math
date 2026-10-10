import OAI.Probability.SLE.Angle.AngleRecurrenceCoefficients

namespace OAI

/-! Finite-degree cancellations used to recover the squared norms of the
monic angular eigenpolynomials from their leading coefficients. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

lemma angleEigenPolynomial_leading_remainder (κ : ℝ) (n : ℕ) :
    (X*angleEigenPolynomial κ n-angleEigenPolynomial κ (n+1)).degree < ((n+1:ℕ):WithBot ℕ) := by
  have hm := monic_X.mul (angleEigenPolynomial_monic κ n)
  have hd : (X*angleEigenPolynomial κ n).degree=(angleEigenPolynomial κ (n+1)).degree := by
    rw [mul_comm,degree_mul_X,degree_eq_natDegree (angleEigenPolynomial_monic κ n).ne_zero,
      degree_eq_natDegree (angleEigenPolynomial_monic κ (n+1)).ne_zero,
      angleEigenPolynomial_natDegree,angleEigenPolynomial_natDegree]
    norm_cast
  have hh := degree_sub_lt_left hd hm.ne_zero
    (by rw [hm,angleEigenPolynomial_monic])
  rw [hd,degree_eq_natDegree (angleEigenPolynomial_monic κ (n+1)).ne_zero,
    angleEigenPolynomial_natDegree] at hh
  exact hh

lemma angleEigenPolynomial_recurrence_remainder {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    (X*angleEigenPolynomial κ (n+2)-angleEigenPolynomial κ (n+3)-
      angleRecurrenceCoefficient κ (n+1) • angleEigenPolynomial κ (n+1)).degree < ((n+1:ℕ):WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro m hm
  rcases eq_or_lt_of_le hm with rfl | hm
  · simp only [coeff_sub,coeff_X_mul,coeff_smul,smul_eq_mul]
    rw [angleEigenPolynomial_coeff κ (n+1) (n+1),angleEigenCoefficient_top]
    have he := angleRecurrenceCoefficient_sub hκ n
    rw [mul_one]
    exact sub_eq_zero.mpr he
  rcases eq_or_lt_of_le (Nat.succ_le_iff.mpr hm) with hm | hm
  · subst m
    rw [show n+1+1=n+2 by omega]
    simp only [coeff_sub,coeff_X_mul,coeff_smul,smul_eq_mul]
    rw [angleEigenPolynomial_penultimate,
      show n+3=(n+2)+1 by omega,angleEigenPolynomial_penultimate,
      angleEigenPolynomial_coeff,angleEigenCoefficient_above κ (by omega)]
    ring
  rcases eq_or_lt_of_le (Nat.succ_le_iff.mpr hm) with hm | hm
  · subst m
    rw [show n+1+1+1=n+3 by omega,show n+3=(n+2)+1 by omega]
    simp only [coeff_sub,coeff_X_mul,coeff_smul,smul_eq_mul,angleEigenPolynomial_coeff]
    rw [angleEigenCoefficient_top,angleEigenCoefficient_top,
      angleEigenCoefficient_above κ (by omega)]
    ring
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ m)
    rw [Nat.add_comm 1 k]
    simp only [coeff_sub,coeff_X_mul,coeff_smul,smul_eq_mul,angleEigenPolynomial_coeff]
    rw [angleEigenCoefficient_above κ (by omega),
      angleEigenCoefficient_above κ (by omega),angleEigenCoefficient_above κ (by omega)]
    ring

lemma angleEigenPolynomial_recurrence_zero {κ : ℝ} (hκ : 0<κ) :
    X*angleEigenPolynomial κ 1-angleEigenPolynomial κ 2-
      angleRecurrenceCoefficient κ 0 • angleEigenPolynomial κ 0=0 := by
  ext m
  rcases m with _|m
  · simp only [coeff_sub,coeff_X_mul_zero,coeff_smul,smul_eq_mul,coeff_zero]
    rw [angleEigenPolynomial_coeff κ 0 0,angleEigenCoefficient_top,
      angleEigenPolynomial_second_coeff hκ 0,
      angleRecurrenceCoefficient_zero]
    norm_num
    field_simp
    ring
  rcases m with _|m
  · simp only [coeff_sub,coeff_X_mul,coeff_smul,smul_eq_mul,coeff_zero]
    rw [show 1=0+1 from rfl,angleEigenPolynomial_penultimate,
      show 2=1+1 from rfl,angleEigenPolynomial_penultimate,
      angleEigenPolynomial_coeff,angleEigenCoefficient_above κ (by omega)]
    ring
  rcases m with _|m
  · simp only [coeff_sub,coeff_X_mul,coeff_smul,smul_eq_mul,coeff_zero,
      angleEigenPolynomial_coeff]
    rw [angleEigenCoefficient_top,angleEigenCoefficient_top,
      angleEigenCoefficient_above κ (by omega)]
    ring
  · simp only [coeff_sub,coeff_X_mul,coeff_smul,smul_eq_mul,coeff_zero,
      angleEigenPolynomial_coeff]
    rw [angleEigenCoefficient_above κ (by omega),
      angleEigenCoefficient_above κ (by omega),angleEigenCoefficient_above κ (by omega)]
    ring

end SLEExactGauge

end

end OAI
