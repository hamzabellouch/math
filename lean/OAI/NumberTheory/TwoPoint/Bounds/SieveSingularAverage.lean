import OAI.NumberTheory.TwoPoint.Bounds.SievePrimeSubsets
import OAI.NumberTheory.TwoPoint.Bounds.SieveSingularLocal
import OAI.NumberTheory.TwoPoint.Bounds.SieveDivisorAverage

namespace OAI

/-! An absolute mean-square bound for the Goldbach singular factor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma sieve_prime_sqrt_product (P : Finset ℕ) :
    (∏ p ∈ P, 1 / Real.sqrt (p : ℝ)) = 1 / Real.sqrt ((∏ p ∈ P, p : ℕ) : ℝ) := by
  simp only [one_div]
  rw [Nat.cast_prod, Real.sqrt_prod P (fun p _ => Nat.cast_nonneg p)]
  exact prod_inv_distrib _

lemma sieve_prime_divisor_subsum {N : ℕ} (hN : N ≠ 0) :
    (∏ p ∈ N.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) ≤
      ∑ d ∈ N.divisors, 1 / Real.sqrt (d : ℝ) := by
  let P := N.primeFactors
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hi := sieve_prime_subset_injective P hP
  have himg : P.powerset.image (fun T => ∏ p ∈ T, p) ⊆ N.divisors := by
    intro d hd
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hd
    apply Nat.mem_divisors.mpr
    exact ⟨(Finset.prod_dvd_prod_of_subset T P (fun p => p) (mem_powerset.mp hT)).trans
      (Nat.prod_primeFactors_dvd N), hN⟩
  calc
    _ = ∑ T ∈ P.powerset, ∏ p ∈ T, 1 / Real.sqrt (p : ℝ) := prod_one_add P
    _ = ∑ T ∈ P.powerset, 1 / Real.sqrt ((∏ p ∈ T, p : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro T _
      exact sieve_prime_sqrt_product T
    _ = ∑ d ∈ P.powerset.image (fun T => ∏ p ∈ T, p), 1 / Real.sqrt (d : ℝ) :=
      (sum_image (f := fun d : ℕ => 1 / Real.sqrt (d : ℝ)) hi).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)

lemma sieve_singular_square_divisor {N : ℕ} (hN : N ≠ 0) :
    sieveSingularFactor N ^ 2 ≤
      (4 : ℝ) ^ 36 * (∑ d ∈ N.divisors, 1 / Real.sqrt (d : ℝ)) :=
  (sieve_singular_square_product N).trans
    (mul_le_mul_of_nonneg_left (sieve_prime_divisor_subsum hN) (by positivity))

noncomputable def sieveSingularMeanConstant : ℝ :=
  (4 : ℝ) ^ 36 * (∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 : ℝ)))

lemma sieve_singular_mean_constant_nonneg : 0 ≤ sieveSingularMeanConstant := by
  unfold sieveSingularMeanConstant
  positivity

/-- An absolute mean square for the singular factor, with no distribution
hypothesis on primes or on the target integer. -/
theorem sieve_singular_square_average (N : ℕ) :
    (∑ n ∈ Icc 1 N, sieveSingularFactor n ^ 2) ≤ sieveSingularMeanConstant * N := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (4 : ℝ) ^ 36 * (∑ d ∈ n.divisors, 1 / Real.sqrt (d : ℝ)) := by
      apply sum_le_sum
      intro n hn
      exact sieve_singular_square_divisor (by have := (mem_Icc.mp hn).1; omega)
    _ = (4 : ℝ) ^ 36 * (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, 1 / Real.sqrt (d : ℝ)) :=
      (mul_sum _ _ _).symm
    _ ≤ (4 : ℝ) ^ 36 * ((N : ℝ) * (∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (sieve_inverse_sqrt_divisor_average N) (by positivity)
    _ = _ := by unfold sieveSingularMeanConstant; ring

end TwoPointCorrelations

end OAI
