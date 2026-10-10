import OAI.NumberTheory.JointDickman.Probability.ArithmeticSplitWeights
import OAI.NumberTheory.JointDickman.Arithmetic.DivisorProductMean

namespace OAI

/-! # Removing a squarefree coefficient from a site without square hits -/

namespace JointDickman
open Finset

theorem primeProduct_dvd_site_iff {B n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    (∏ p ∈ A, p) ∣ n ↔ A ⊆ coefficientPrimeSet B n := by
  rw [primeProduct_dvd_iff A (fun p hp => auxiliaryPrimes_prime B p (hA hp))]
  constructor
  · intro h p hp
    exact mem_filter.mpr ⟨hA hp, h p hp⟩
  · intro h p hp
    exact (mem_filter.mp (h hp)).2

/-- The quotient prime set is the complementary subset when none of the
selected site primes has a square dividing the original integer. -/
theorem coefficientPrimeSet_quotient {B n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (ha : (∏ p ∈ A, p) ∣ n)
    (hno : ∀ p ∈ auxiliaryPrimes B, ¬ p^2 ∣ n) :
    coefficientPrimeSet B (n / (∏ p ∈ A, p)) = coefficientPrimeSet B n \ A := by
  have he : (∏ p ∈ A, p) * (n / (∏ p ∈ A, p)) = n := Nat.mul_div_cancel' ha
  have hpos : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr
    (fun p hp => (auxiliaryPrimes_prime B p (hA hp)).ne_zero)
  have hf : (∏ p ∈ A, p).primeFactors = A :=
    Nat.primeFactors_prod (fun p hp => auxiliaryPrimes_prime B p (hA hp))
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hpq⟩ := mem_filter.mp hp
    have hpn : p ∣ n := by rw [← he]; exact dvd_mul_of_dvd_right hpq _
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hpP, hpn⟩, ?_⟩
    intro hpA
    have hpa : p ∣ ∏ p ∈ A, p := dvd_prod_of_mem id hpA
    have hsq : p^2 ∣ n := by
      rw [pow_two, ← he]
      exact Nat.mul_dvd_mul hpa hpq
    exact hno p hpP hsq
  · intro hp
    obtain ⟨hpn, hpA⟩ := mem_sdiff.mp hp
    obtain ⟨hpP, hpn⟩ := mem_filter.mp hpn
    have hprime := auxiliaryPrimes_prime B p hpP
    have hpa : ¬ p ∣ ∏ p ∈ A, p := by
      intro h
      have hm := hprime.mem_primeFactors h hpos
      rw [hf] at hm
      exact hpA hm
    refine mem_filter.mpr ⟨hpP, ?_⟩
    rw [← he] at hpn
    exact (hprime.dvd_mul.mp hpn).resolve_left hpa

end JointDickman

end OAI
