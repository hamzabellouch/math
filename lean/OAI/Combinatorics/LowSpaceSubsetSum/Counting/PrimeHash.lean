import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

namespace OAI

/-!
# The bit-length dependence in prime hashing

The prime range has an explicit cardinality lower bound. Counting distinct
prime divisors of a nonzero weight difference then gives the manuscript's
`lem:prime`, with the full dependence on the bit-length parameter.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

/-- The finite prime range used by all modular filters. -/
def primeRange (ell : ℕ) : Finset ℕ :=
  (Nat.primesLE (2 ^ ell)).filter fun p => 2 ^ ell ≤ 4 * ell * p

theorem primeRange_prime {ell p : ℕ} (hp : p ∈ primeRange ell) : p.Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1

theorem primeRange_lt {ell p : ℕ} (hell : 4 ≤ ell) (hp : p ∈ primeRange ell) :
    p < 2 ^ ell := by
  have hle := Nat.le_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hne : p ≠ 2 ^ ell := by
    intro h
    exact Nat.Prime.not_prime_pow (by omega : 2 ≤ ell) (h ▸ primeRange_prime hp)
  exact lt_of_le_of_ne hle hne

private theorem two_mul_succ_le_pow {ell : ℕ} (hell : 4 ≤ ell) :
    2 * (ell + 1) ≤ 2 ^ ell := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hell
  induction k with
  | zero => norm_num
  | succ k ih =>
    have ih' := ih (by omega)
    rw [show 4 + (k + 1) = (4 + k) + 1 by omega, pow_succ]
    nlinarith

/-- The elementary prime-counting lower bound needed for the sampling range. -/
theorem primeCounting_power_two_lower {ell : ℕ} (hell : 4 ≤ ell) :
    2 ^ ell ≤ 2 * ell * (2 ^ ell).primeCounting := by
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hX1 : (1 : ℝ) < (2 ^ ell : ℕ) := by
    exact_mod_cast (one_lt_pow₀ (by decide : (1 : ℕ) < 2) (by omega : ell ≠ 0))
  have hlog : Real.log (2 ^ ell : ℕ) = (ell : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hXpos : (0 : ℝ) < (2 ^ ell : ℕ) := lt_trans (by norm_num) hX1
  have hlogs : Real.log ((2 ^ ell : ℕ) + 1) ≤ (ell + 1 : ℝ) * Real.log 2 := by
    have hle : ((2 ^ ell : ℕ) : ℝ) + 1 ≤ 2 * (2 ^ ell : ℕ) := by linarith
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 ^ ell : ℕ) + 1) hle
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne', hlog] at h
    nlinarith
  have hs : (ell + 1 : ℝ) ≤ (2 ^ ell : ℕ) / 2 := by
    have h := two_mul_succ_le_pow hell
    have hr : (2 : ℝ) * (ell + 1) ≤ (2 ^ ell : ℕ) := by exact_mod_cast h
    linarith
  have hpi := Chebyshev.pi_ge (2 ^ ell)
  have hpi' := (div_le_iff₀ (Real.log_pos hX1)).mp hpi
  rw [hlog] at hpi'
  have hbound : ((2 ^ ell : ℕ) : ℝ) / 2 * Real.log 2 ≤
      (ell : ℝ) * (2 ^ ell).primeCounting * Real.log 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hs htwo.le]
  have hbound' := (mul_le_mul_iff_left₀ htwo).mp hbound
  have hr : ((2 ^ ell : ℕ) : ℝ) ≤ 2 * ell * (2 ^ ell).primeCounting := by
    linarith
  exact_mod_cast hr

/-- At least `2^ell/(4 ell)` primes lie in the manuscript's finite range. -/
theorem primeRange_card_lower {ell : ℕ} (hell : 4 ≤ ell) :
    2 ^ ell ≤ 4 * ell * (primeRange ell).card := by
  let bad := (Nat.primesLE (2 ^ ell)).filter fun p => 4 * ell * p < 2 ^ ell
  have hbadsub : bad ⊆ Finset.Icc 1 (2 ^ ell / (4 * ell)) := by
    intro p hp
    obtain ⟨hpp, hplt⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_Icc.mpr
    refine ⟨(Nat.prime_of_mem_primesLE hpp).one_le, ?_⟩
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4 * ell)).mpr
    simpa only [mul_comm] using hplt.le
  have hbadcard : bad.card ≤ 2 ^ ell / (4 * ell) := by
    simpa using Finset.card_le_card hbadsub
  have hbad : 4 * ell * bad.card ≤ 2 ^ ell :=
    (Nat.mul_le_mul_left (4 * ell) hbadcard).trans (Nat.mul_div_le _ _)
  have hpartition : (primeRange ell).card + bad.card = (2 ^ ell).primeCounting := by
    have h := Finset.card_filter_add_card_filter_not
      (s := Nat.primesLE (2 ^ ell)) (p := fun p => 2 ^ ell ≤ 4 * ell * p)
    simpa only [primeRange, bad, not_le, Nat.primesLE_card_eq_primeCounting] using h
  have hpi := primeCounting_power_two_lower hell
  nlinarith

theorem two_pow_card_primeFactors_le {d : ℕ} (hd : 0 < d) :
    2 ^ d.primeFactors.card ≤ d := by
  calc
    2 ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ d.primeFactors, p := by
      apply Finset.prod_le_prod
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ d := Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)

/-- A nonzero `K`-bit integer has fewer than `K` distinct prime divisors. -/
theorem card_primeFactors_lt {d K : ℕ} (hd : 0 < d) (hbits : d < 2 ^ K) :
    d.primeFactors.card < K := by
  have hp := (two_pow_card_primeFactors_le hd).trans_lt hbits
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp

/-- All sampled divisors are among the distinct prime factors of the difference. -/
theorem card_sampled_prime_divisors_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {d K : ℕ} (hd : 0 < d) (hbits : d < 2 ^ K) :
    (P.filter fun p => p ∣ d).card ≤ K := by
  have hsub : (P.filter fun p => p ∣ d) ⊆ d.primeFactors := by
    intro p hp
    obtain ⟨hpP, hpd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hP p hpP, hpd, by omega⟩
  exact (Finset.card_le_card hsub).trans (card_primeFactors_lt hd hbits).le

/-- Uniform prime hashing with its explicit polynomial-bit loss. -/
theorem prime_divisor_probability_le {ell u d : ℕ}
    (hell : 4 ≤ ell) (hellu : ell ≤ u) (hd : 0 < d) (hbits : d < 2 ^ (2 * u)) :
    (((primeRange ell).filter fun p => p ∣ d).card : ℝ) / (primeRange ell).card ≤
      8 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ell := by
  have hcard := primeRange_card_lower hell
  have hpos : 0 < (primeRange ell).card := by
    have hpow : 0 < 2 ^ ell := pow_pos (by decide) _
    nlinarith
  have hposR : (0 : ℝ) < (primeRange ell).card := by exact_mod_cast hpos
  have hpowR : (0 : ℝ) < (2 : ℝ) ^ ell := pow_pos (by norm_num) _
  have hC : (((primeRange ell).filter fun p => p ∣ d).card : ℝ) ≤ 2 * u := by
    exact_mod_cast card_sampled_prime_divisors_le (primeRange ell)
      (fun _ hp => primeRange_prime hp) hd hbits
  have hD : (2 : ℝ) ^ ell ≤ 4 * ell * (primeRange ell).card := by
    exact_mod_cast hcard
  have helluR : (ell : ℝ) ≤ u := by exact_mod_cast hellu
  apply (div_le_div_iff₀ hposR hpowR).mpr
  calc
    _ ≤ (2 * u : ℝ) * (2 : ℝ) ^ ell :=
      mul_le_mul_of_nonneg_right hC hpowR.le
    _ ≤ (2 * u : ℝ) * (4 * ell * (primeRange ell).card) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ ≤ 8 * (u : ℝ) ^ 2 * (primeRange ell).card := by
      nlinarith [mul_nonneg (sub_nonneg.mpr helluR)
        (show 0 ≤ (u : ℝ) * (primeRange ell).card by positivity)]

end LowSpaceSubsetSum

end OAI
