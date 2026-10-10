import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Prime-divisor budget in the collision argument

A distinct pair of integers at distance at most `X` contributes at most
`log X` to the sum of `log p` over primes at which it collides. This is the
elementary counting step behind the larger-sieve use in §§2–3.
-/

namespace Ostmann

open scoped BigOperators

/-- Distinct prime divisors of a positive integer have total logarithmic
weight at most the logarithm of that integer. -/
theorem sum_log_prime_divisors_le (P : Finset ℕ) {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ∣ n) :
    ∑ p ∈ P, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hsub : P ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdiv p hp, Nat.ne_of_gt hn⟩
  have hprod_dvd : (∏ p ∈ P, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset P n.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd n)
  have hprod_pos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  have hprod_le : (∏ p ∈ P, p) ≤ n := Nat.le_of_dvd hn hprod_dvd
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (hprime p hp).ne_zero),
    ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hprod_pos) (by exact_mod_cast hprod_le)

/-- The off-diagonal prime-collision budget, in the ordered-pair convention. -/
theorem sum_log_congruent_primes_le_of_sub_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hdiff : y - x ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) := by
  have hpos : 0 < y - x := Nat.sub_pos_of_lt hxy
  have hbudget := sum_log_prime_divisors_le (P.filter (fun p => x ≡ y [MOD p])) hpos
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2.dvd')
  exact hbudget.trans (Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast hdiff))

/-- The collision budget for a pair in the initial interval `[0,X]`. -/
theorem sum_log_congruent_primes_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hy : y ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) :=
  sum_log_congruent_primes_le_of_sub_le P hxy ((Nat.sub_le y x).trans hy) hprime

end Ostmann

end OAI
