import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337

/-- A gcd of a product divides the product of the individual gcds. -/
theorem gcd_prod_dvd_prod_gcd {ι : Type*} (s : Finset ι) (p : ι → ℕ) (u : ℕ) :
    Nat.gcd (∏ i ∈ s, p i) u ∣ ∏ i ∈ s, Nat.gcd (p i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have h : Nat.gcd (p i * ∏ j ∈ s, p j) u ∣
          Nat.gcd (p i) u * Nat.gcd (∏ j ∈ s, p j) u := by
        simpa only [gcd_eq_nat_gcd, Nat.gcd_comm] using
          (gcd_mul_dvd_mul_gcd u (p i) (∏ j ∈ s, p j))
      exact h.trans (Nat.mul_dvd_mul_left _ ih)

/-- Only prime samples that divide the modulus contribute to its gcd with
    the sampled product, even when sampled values repeat. -/
theorem gcd_prime_product_dvd_hits {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u : ℕ) (hp : ∀ i ∈ s, (p i).Prime) :
    Nat.gcd (∏ i ∈ s, p i) u ∣ ∏ i ∈ s.filter (fun i => p i ∣ u), p i := by
  classical
  have heq : (∏ i ∈ s, Nat.gcd (p i) u) =
      ∏ i ∈ s.filter (fun i => p i ∣ u), p i := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : p i ∣ u
    · simp [h, Nat.gcd_eq_left_iff_dvd.mpr h]
    · simp [h, ((hp i hi).coprime_iff_not_dvd.mpr h).gcd_eq_one]
  rw [← heq]
  exact gcd_prod_dvd_prod_gcd s p u

/-- Bounded sampled primes give a power bound in the number of hits. -/
theorem gcd_prime_product_le_pow_hits {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u B : ℕ) (hp : ∀ i ∈ s, (p i).Prime) (hB : ∀ i ∈ s, p i ≤ B) :
    Nat.gcd (∏ i ∈ s, p i) u ≤ B ^ (s.filter (fun i => p i ∣ u)).card := by
  classical
  have hpos : 0 < ∏ i ∈ s.filter (fun i => p i ∣ u), p i := by
    apply Finset.prod_pos
    intro i hi
    exact (hp i (Finset.mem_filter.mp hi).1).pos
  apply (Nat.le_of_dvd hpos (gcd_prime_product_dvd_hits s p u hp)).trans
  apply Finset.prod_le_pow_card
  intro i hi
  exact hB i (Finset.mem_filter.mp hi).1

/-- The extra frequency factor costs at most its full size. -/
theorem gcd_frequency_prime_product_le {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u B l : ℕ) (hp : ∀ i ∈ s, (p i).Prime)
    (hB : ∀ i ∈ s, p i ≤ B) (hl : 0 < l) :
    Nat.gcd (l * ∏ i ∈ s, p i) u ≤ l * B ^ (s.filter (fun i => p i ∣ u)).card := by
  classical
  have hg : Nat.gcd (l * ∏ i ∈ s, p i) u ∣
      Nat.gcd l u * Nat.gcd (∏ i ∈ s, p i) u := by
    simpa only [gcd_eq_nat_gcd, Nat.gcd_comm] using
      gcd_mul_dvd_mul_gcd u l (∏ i ∈ s, p i)
  have hprod : 0 < ∏ i ∈ s, p i := Finset.prod_pos (fun i hi => (hp i hi).pos)
  have hpos : 0 < Nat.gcd l u * Nat.gcd (∏ i ∈ s, p i) u := by
    exact Nat.mul_pos (Nat.gcd_pos_of_pos_left u hl) (Nat.gcd_pos_of_pos_left u hprod)
  exact (Nat.le_of_dvd hpos hg).trans (Nat.mul_le_mul
    (Nat.gcd_le_left u hl) (gcd_prime_product_le_pow_hits s p u B hp hB))

/-- A set of distinct prime divisors, all at least `L`, has size bounded
    by the logarithm of the modulus. This bounds the population of hit values. -/
theorem prime_divisor_population_pow_le (P : Finset ℕ) (u L : ℕ)
    (hu : 0 < u) (hp : ∀ p ∈ P, p.Prime) (hL : ∀ p ∈ P, L ≤ p) :
    L ^ (P.filter (fun p => p ∣ u)).card ≤ u := by
  have hsub : P.filter (fun p => p ∣ u) ⊆ u.primeFactors := by
    intro p h
    obtain ⟨hpP, hpu⟩ := Finset.mem_filter.mp h
    exact Nat.mem_primeFactors.mpr ⟨hp p hpP, hpu, hu.ne'⟩
  have hdvd : (∏ p ∈ P.filter (fun p => p ∣ u), p) ∣ u :=
    (Finset.prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd u)
  calc
    L ^ (P.filter (fun p => p ∣ u)).card ≤
        ∏ p ∈ P.filter (fun p => p ∣ u), p := by
      apply Finset.pow_card_le_prod
      intro p h
      exact hL p (Finset.mem_filter.mp h).1
    _ ≤ u := Nat.le_of_dvd hu hdvd

/-- Real logarithmic version of the prime hit population estimate. -/
theorem prime_divisor_population_log_le (P : Finset ℕ) (u L : ℕ)
    (hu : 0 < u) (hL1 : 1 < L)
    (hp : ∀ p ∈ P, p.Prime) (hL : ∀ p ∈ P, L ≤ p) :
    ((P.filter (fun p => p ∣ u)).card : ℝ) ≤
      Real.log (u : ℝ) / Real.log (L : ℝ) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hpow := prime_divisor_population_pow_le P u L hu hp hL
  have hreal : (L : ℝ) ^ (P.filter (fun p => p ∣ u)).card ≤ u := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos hLpos _) hreal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hL1))).mpr hlog

end Problem337

end OAI
