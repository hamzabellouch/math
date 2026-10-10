import OAI.NumberTheory.TwoPoint.Bounds.SievePrimeSubsets
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass

namespace OAI

/-! The logarithmic-moment criterion applied to the actual Goldbach sieve. -/

namespace TwoPointCorrelations

open Finset Problem337
open scoped Classical

lemma sieve_prime_subset_log_cutoff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {z : ℕ} (hz : 0 < z) :
    (∑ p ∈ P, Real.log p) ≤ Real.log z ↔ (∏ p ∈ P, p) ≤ z := by
  have hp : 0 < ∏ p ∈ P, (p : ℝ) :=
    prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos)
  rw [← sieve_prime_subset_log P hP, Real.log_le_log_iff hp (by exact_mod_cast hz)]
  rw [← Nat.cast_prod]
  exact Nat.cast_le

theorem sieve_goldbach_denominator_half_product (N z : ℕ) (hN : 2 ∣ N) (hz : 2 ≤ z)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hmean : 2 * (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ Real.log z / 2) :
    (∏ p ∈ P, (1 + sieveGoldbachWeight N p)) / 2 ≤
      GoldbachSelberg.denominator N (primorial z) z := by
  have hz0 : (0 : ℝ) < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have he := sieve_euler_truncation P (sieveGoldbachWeight N) (fun p => Real.log p)
    (fun p hp => (sieve_goldbach_weight_pos hN (hP p hp)).le)
    (fun p hp => Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) hz0
    ((sieve_goldbach_mean_le hN P hP).trans hmean)
  have hsets : P.powerset.filter (fun T : Finset ℕ => (∑ p ∈ T, Real.log (p : ℝ)) ≤ Real.log z) =
      P.powerset.filter (fun T => (∏ p ∈ T, p) ≤ z) := by
    ext T
    simp only [mem_filter]
    constructor
    · rintro ⟨hT, h⟩
      exact ⟨hT, (sieve_prime_subset_log_cutoff T
        (fun p hp => hP p (mem_powerset.mp hT hp)) (by omega)).mp h⟩
    · rintro ⟨hT, h⟩
      exact ⟨hT, (sieve_prime_subset_log_cutoff T
        (fun p hp => hP p (mem_powerset.mp hT hp)) (by omega)).mpr h⟩
  rw [hsets] at he
  exact he.trans (sieve_prime_subset_denominator N z hN P hP)

/-- The small-prime cutoff is chosen using a logarithmic inequality, avoiding
any rounding assumption on its real value. -/
theorem sieve_goldbach_denominator_small_primes (N z : ℕ) (hN : 2 ∣ N) (hz : 2 ≤ z)
    {y : ℝ} (hy : 1 ≤ y)
    (hscale : 4 * (Real.log y + halaszMertensConstant) ≤ Real.log z) :
    (∏ p ∈ sievePrimesUpTo y, (1 + sieveGoldbachWeight N p)) / 2 ≤
      GoldbachSelberg.denominator N (primorial z) z := by
  apply sieve_goldbach_denominator_half_product N z hN hz (sievePrimesUpTo y)
    (sievePrimesUpTo_prime y)
  linarith [halasz_prime_prefix_mass_le hy]

end TwoPointCorrelations

end OAI
