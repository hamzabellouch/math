import Mathlib.Data.Nat.Factorization.Basic
import OAI.NumberTheory.SiegelZeros.Characters.CharacterMaster

namespace OAI

section

namespace SiegelZeros.W07
open scoped BigOperators

theorem primeWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ primeWeight p := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) (Nat.cast_nonneg p)

theorem primeWeight_le_log {p : ℕ} (hp : p.Prime) : primeWeight p ≤ Real.log p := by
  exact div_le_self (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    (by exact_mod_cast hp.one_lt.le)

theorem ramified_prime_mass_le_log {q : ℕ} (hq : 0 < q) :
    primeMass q.primeFactors ≤ Real.log q := by
  calc
    primeMass q.primeFactors ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact primeWeight_le_log (Nat.prime_of_mem_primeFactors hp)
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
      symm
      apply Real.log_prod
      intro p hp
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ Real.log q := by
      apply Real.log_le_log
      · apply Finset.prod_pos
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      · rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)

theorem zero_value_mass_le_log {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hq : 0 < q) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    primeMass (valuePrimes χ S 0) ≤ Real.log q := by
  classical
  apply le_trans _ (ramified_prime_mass_le_log hq)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hs, hz⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hS p hs, (prime_value_zero_iff_dvd χ (hS p hs)).mp hz,
      Nat.ne_of_gt hq⟩
  · intro p hp hn
    exact primeWeight_nonneg (Nat.prime_of_mem_primeFactors hp)

noncomputable def smallPrimeMass (H : ℕ) : ℝ :=
  primeMass ((Finset.range (H + 1)).filter Nat.Prime)

theorem discarded_mass_le_smallPrimeMass {q H : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hH : 2 ≤ H) :
    primeMass (discardedNegativePrimes χ S H) ≤ smallPrimeMass H := by
  classical
  rw [discarded_eq_small_negative χ S hS hH]
  unfold smallPrimeMass primeMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hv, hsmall⟩ := Finset.mem_filter.mp hp
    obtain ⟨hs, _⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hS p hs⟩
  · intro p hp hn
    exact primeWeight_nonneg (Finset.mem_filter.mp hp).2

theorem good_mass_from_primebias_mertens {q H : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (hq : 0 < q) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hH : 2 ≤ H) (logX delta C Bm : ℝ)
    (mertens : logX - Bm ≤ primeMass S)
    (primebias : primeMass (valuePrimes χ S 1) ≤
      C * Real.log q + C * delta * logX ^ 2 / Real.log q) :
    logX - (C + 1) * Real.log q - C * delta * logX ^ 2 / Real.log q -
      (Bm + smallPrimeMass H) ≤ primeMass (goodPrimes χ S H) := by
  have h := good_mass_lower_bound χ hχ S H logX (Real.log q) delta C Bm
    (Real.log q) (smallPrimeMass H) mertens primebias
    (zero_value_mass_le_log χ hq S hS) (discarded_mass_le_smallPrimeMass χ S hS hH)
  linarith

end SiegelZeros.W07

end

end OAI
