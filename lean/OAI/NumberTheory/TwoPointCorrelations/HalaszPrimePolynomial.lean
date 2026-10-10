import OAI.NumberTheory.TwoPointCorrelations.HalaszWindowIntegral
import OAI.NumberTheory.TwoPointCorrelations.HalaszSmoothSeries

namespace OAI

/-! The finite prime factors in the Perron integrand, with the same
normalization as the prime mean-square theorem. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

noncomputable def halaszPrimePolynomial (P : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial P
    (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ)) (fun p => -Real.log (p : ℝ)) t

lemma halasz_prime_polynomial_series (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    (∑ p ∈ P, LSeries.term (fun p => (Real.log (p : ℝ) : ℂ) * a p)
      (1 + (t : ℂ) * I) p) = halaszPrimePolynomial P a t := by
  unfold halaszPrimePolynomial mrtExponentialPolynomial
  apply sum_congr rfl
  intro p hp
  rw [mrt_line_one_term _ (hP p hp).ne_zero t]
  push_cast
  ring

lemma halasz_prime_polynomial_continuous (P : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (halaszPrimePolynomial P a) := halasz_polynomial_continuous P _ _

lemma halasz_prime_polynomial_norm (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    ‖halaszPrimePolynomial P a t‖ ≤ ∑ p ∈ P, ‖a p‖ * (Real.log (p : ℝ) / p) := by
  apply (halasz_polynomial_norm_le P _ _ t).trans_eq
  apply sum_congr rfl
  intro p hp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)

lemma halasz_prime_polynomial_bounded (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) {R : ℝ} (ha : ∀ p ∈ P, ‖a p‖ ≤ R) (t : ℝ) :
    ‖halaszPrimePolynomial P a t‖ ≤ R * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  apply (halasz_prime_polynomial_norm P a hP t).trans
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (ha p hp)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _))

lemma halasz_prime_coefficient_square_mass (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) {R : ℝ} (ha : ∀ p ∈ P, ‖a p‖ ≤ R) :
    (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) ≤
      R ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha p hp) 2)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _))

lemma halasz_adaptive_coefficient_bound (f : ℕ → ℂ) (hf : OneBounded f)
    {X v : ℝ} (hv : 0 < v) {p : ℕ} (hp : 0 < p)
    (hlog : v ≤ Real.log (X / p)) :
    ‖f p / (Real.log (X / p) : ℂ)‖ ≤ v⁻¹ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hv.trans_le hlog)]
  exact (div_le_div_of_nonneg_right (hf p hp) (hv.le.trans hlog)).trans
    (by simpa only [one_div] using one_div_le_one_div_of_le hv hlog)

lemma halasz_finite_prime_mangoldt_bound (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) {R : ℝ} (hR : 0 ≤ R) (ha : ∀ p ∈ P, ‖a p‖ ≤ R) (n : ℕ) :
    ‖halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) n‖ ≤
      R * ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n ∈ P
  · rw [halaszFiniteCoefficient, ite_eq_left hn, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (hP n hn).one_le)),
      ArithmeticFunction.vonMangoldt_apply_prime (hP n hn)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (ha n hn)
      (Real.log_nonneg (by exact_mod_cast (hP n hn).one_le))
  · rw [halaszFiniteCoefficient, ite_eq_right hn, norm_zero]
    exact mul_nonneg hR ArithmeticFunction.vonMangoldt_nonneg

end TwoPointCorrelations

end OAI
