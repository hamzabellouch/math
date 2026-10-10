import Mathlib

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

theorem sum_log_prime_divisors_le (P : Finset ℕ) (N : ℕ) (hN : N ≠ 0)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hdiv : ∀ p ∈ P, p ∣ N) :
    ∑ p ∈ P, Real.log p ≤ Real.log N := by
  have hsubset : P ⊆ N.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdiv p hp, hN⟩
  have hprod_dvd : (∏ p ∈ P, p) ∣ N :=
    (Finset.prod_dvd_prod_of_subset P N.primeFactors id hsubset).trans
      (Nat.prod_primeFactors_dvd N)
  have hprod_pos : 0 < ∏ p ∈ P, p :=
    Finset.prod_pos (fun p hp => (hprime p hp).pos)
  calc
    (∑ p ∈ P, Real.log p) = Real.log (∏ p ∈ P, (p : ℝ)) := by
      rw [Real.log_prod]
      intro p hp
      exact_mod_cast (hprime p hp).ne_zero
    _ = Real.log ((∏ p ∈ P, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
    _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast hprod_pos)
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hprod_dvd)

theorem sum_log_prime_divisors_int_le (P : Finset ℕ) (d : ℤ) (hd : d ≠ 0)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ d) :
    ∑ p ∈ P, Real.log p ≤ Real.log d.natAbs := by
  apply sum_log_prime_divisors_le P d.natAbs (by simpa using hd) hprime
  intro p hp
  exact Int.natCast_dvd.mp (hdiv p hp)

theorem sum_log_congruent_primes_le (P : Finset ℕ) (n m X : ℕ)
    (hne : n ≠ m) (hn : n ≤ X) (hm : m ≤ X)
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    (∑ p ∈ P.filter (fun p => (n : ZMod p) = (m : ZMod p)), Real.log p) ≤
      Real.log X := by
  let d : ℤ := (m : ℤ) - n
  have hd : d ≠ 0 := by dsimp [d]; exact sub_ne_zero.mpr (by exact_mod_cast hne.symm)
  have hbound := sum_log_prime_divisors_int_le
    (P.filter (fun p => (n : ZMod p) = (m : ZMod p))) d hd
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => Nat.modEq_iff_dvd.mp
      ((ZMod.natCast_eq_natCast_iff n m p).mp (Finset.mem_filter.mp hp).2))
  have hpos : (0 : ℝ) < d.natAbs := by
    exact_mod_cast (Int.natAbs_pos.mpr hd)
  have hle : (d.natAbs : ℝ) ≤ X := by
    have hleI : (d.natAbs : ℤ) ≤ X := by
      rw [Int.natCast_natAbs]
      dsimp [d]
      exact abs_le.mpr ⟨by omega, by omega⟩
    exact_mod_cast hleI
  exact hbound.trans (Real.log_le_log hpos hle)

theorem sum_log_primesLE_le (Q : ℕ) :
    ∑ p ∈ Q.primesLE, Real.log p ≤ Real.log 4 * Q := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (by positivity)

end Ostmann.Preliminaries

end OAI
