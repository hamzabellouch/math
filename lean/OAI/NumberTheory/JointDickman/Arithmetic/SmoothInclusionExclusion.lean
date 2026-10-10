import OAI.NumberTheory.JointDickman.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Exact finite inclusion-exclusion for smoothness

For a finite set of distinct primes, expand the product of their avoidance
indicators and count multiples of each squarefree prime product. The result
is an exact identity; no prime asymptotic or correlation input is used here.
-/

namespace JointDickman

open Finset

/-- The integers `1 ≤ n ≤ N` with no factor among the excluded primes. -/
noncomputable def excludedPrimeCount (E : Finset ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc 0 N).filter (fun n => ∀ p ∈ E, ¬p ∣ n)).card

theorem primeProduct_dvd_iff (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) (n : ℕ) :
    (∏ p ∈ E, p) ∣ n ↔ ∀ p ∈ E, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun p : ℕ => p) hp).trans h
  · exact Finset.prod_primes_dvd n (fun p hp => (hE p hp).prime)

private theorem avoidance_indicator (E : Finset ℕ) (n : ℕ) :
    (if ∀ p ∈ E, ¬p ∣ n then (1 : ℝ) else 0) =
      ∏ p ∈ E, (1 - if p ∣ n then (1 : ℝ) else 0) := by
  classical
  by_cases h : ∀ p ∈ E, ¬p ∣ n
  · rw [ite_eq_left h]
    symm
    exact Finset.prod_eq_one fun p hp => by simp [h p hp]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨p, hp, hpn⟩ := h
    symm
    exact Finset.prod_eq_zero hp (by simp [hpn])

private theorem divisor_indicator_product (E : Finset ℕ)
    (hE : ∀ p ∈ E, p.Prime) (n : ℕ) :
    (∏ p ∈ E, if p ∣ n then (1 : ℝ) else 0) =
      if (∏ p ∈ E, p) ∣ n then 1 else 0 := by
  classical
  by_cases h : (∏ p ∈ E, p) ∣ n
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one fun p hp => by
      simp [(primeProduct_dvd_iff E hE n).mp h p hp]
  · rw [ite_eq_right h]
    have hall : ¬∀ p ∈ E, p ∣ n := fun hh => h ((primeProduct_dvd_iff E hE n).mpr hh)
    push Not at hall
    obtain ⟨p, hp, hpn⟩ := hall
    exact Finset.prod_eq_zero hp (by simp [hpn])

/-- The finite inclusion-exclusion identity before averaging. -/
theorem prime_avoidance_inclusion_exclusion (E : Finset ℕ)
    (hE : ∀ p ∈ E, p.Prime) (n : ℕ) :
    (if ∀ p ∈ E, ¬p ∣ n then (1 : ℝ) else 0) =
      ∑ s ∈ E.powerset, (-1 : ℝ) ^ s.card *
        (if (∏ p ∈ s, p) ∣ n then 1 else 0) := by
  classical
  rw [avoidance_indicator, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  simp only [Finset.prod_const_one, mul_one]
  rw [divisor_indicator_product s (fun p hp => hE p (hsE hp)) n]

private theorem sum_divisor_indicator (N d : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, if d ∣ n then (1 : ℝ) else 0) = (N / d : ℕ) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  simp

/-- The exact floor formula for integers avoiding a finite set of primes.
Natural division on the right is `floor(N / product(s))`. -/
theorem excludedPrimeCount_eq_inclusion_exclusion (E : Finset ℕ)
    (hE : ∀ p ∈ E, p.Prime) (N : ℕ) :
    (excludedPrimeCount E N : ℝ) =
      ∑ s ∈ E.powerset, (-1 : ℝ) ^ s.card * (N / (∏ p ∈ s, p) : ℕ) := by
  classical
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N, if ∀ p ∈ E, ¬p ∣ n then (1 : ℝ) else 0 := by
      simp [excludedPrimeCount]
    _ = ∑ n ∈ Finset.Ioc 0 N,
        ∑ s ∈ E.powerset, (-1 : ℝ) ^ s.card *
          (if (∏ p ∈ s, p) ∣ n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n _
      exact prime_avoidance_inclusion_exclusion E hE n
    _ = ∑ s ∈ E.powerset, (-1 : ℝ) ^ s.card *
        ∑ n ∈ Finset.Ioc 0 N, if (∏ p ∈ s, p) ∣ n then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [sum_divisor_indicator]

/-- The primes that prevent an integer up to `N` from being `y`-smooth. -/
noncomputable def excludedSmoothnessPrimes (N : ℕ) (y : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 N).filter (fun p => p.Prime ∧ y < (p : ℝ))

/-- On `1 ≤ n ≤ N`, avoidance of the finite excluded set is smoothness. -/
theorem maxPrimeFac_le_iff_avoids_excluded {N n : ℕ} {y : ℝ}
    (hy : 1 ≤ y) (hn : 1 ≤ n) (hnN : n ≤ N) :
    (n.maxPrimeFac : ℝ) ≤ y ↔ ∀ p ∈ excludedSmoothnessPrimes N y, ¬p ∣ n := by
  classical
  constructor
  · intro hs p hp hpn
    have hpp : p.Prime ∧ y < (p : ℝ) := (Finset.mem_filter.mp hp).2
    have hle : (p : ℝ) ≤ n.maxPrimeFac := by
      exact_mod_cast Nat.le_maxPrimeFac (by omega) hpp.1 hpn
    linarith
  · intro ha
    by_cases hone : n = 1
    · simpa [hone] using hy
    by_contra hs
    have hp := Nat.prime_maxPrimeFac_of_one_lt (by omega : 1 < n)
    have hmem : n.maxPrimeFac ∈ excludedSmoothnessPrimes N y := by
      simp only [excludedSmoothnessPrimes, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp.two_le, Nat.maxPrimeFac_le.trans hnN⟩, hp, lt_of_not_ge hs⟩
    exact ha _ hmem Nat.maxPrimeFac_dvd

/-- The exact inclusion-exclusion formula for the ordinary smooth count. -/
theorem smoothCount_eq_inclusion_exclusion (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (((Finset.Ioc 0 N).filter (fun n => (n.maxPrimeFac : ℝ) ≤ y)).card : ℝ) =
      ∑ s ∈ (excludedSmoothnessPrimes N y).powerset,
        (-1 : ℝ) ^ s.card * (N / (∏ p ∈ s, p) : ℕ) := by
  classical
  have hfilter : (Finset.Ioc 0 N).filter (fun n => (n.maxPrimeFac : ℝ) ≤ y) =
      (Finset.Ioc 0 N).filter (fun n => ∀ p ∈ excludedSmoothnessPrimes N y, ¬p ∣ n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact maxPrimeFac_le_iff_avoids_excluded hy (by omega) hn'.2
  rw [hfilter]
  exact excludedPrimeCount_eq_inclusion_exclusion (excludedSmoothnessPrimes N y)
    (fun p hp => (Finset.mem_filter.mp hp).2.1) N

end JointDickman

end OAI
