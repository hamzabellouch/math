import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import OAI.NumberTheory.Ostmann.Arithmetic.UnitSquareRoots

namespace OAI

/-! # The divisor loss in the square-congruence probability -/

namespace Ostmann

open scoped BigOperators Classical

theorem two_pow_primeFactors_card_le_divisors_card (q : ℕ) (hq : q ≠ 0) :
    2 ^ q.primeFactors.card ≤ q.divisors.card := by
  rw [Nat.card_divisors hq]
  calc
    _ = ∏ _p ∈ q.primeFactors, 2 := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod
      intro p hp
      have hmem : p ∈ q.factorization.support := by
        simpa only [Nat.support_factorization] using hp
      have hf := Finsupp.mem_support_iff.mp hmem
      omega

theorem le_divisors_card_mul_totient (q : ℕ) (hq : q ≠ 0) :
    q ≤ q.divisors.card * q.totient := by
  calc
    _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
    _ ≤ ∑ _d ∈ q.divisors, q.totient := Finset.sum_le_sum fun d hd =>
      Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = _ := by simp

/-- The loss from unit sampling and the possible power of two is bounded
by two divisor factors, leaving the essential reciprocal-modulus decay. -/
theorem square_root_density_factor_le (q : ℕ) [NeZero q] :
    (2 : ℝ) ^ (q.primeFactors.card + 1) / q.totient ≤
      2 * (q.divisors.card : ℝ) ^ 2 / q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hω : (2 : ℝ) ^ q.primeFactors.card ≤ q.divisors.card := by
    exact_mod_cast two_pow_primeFactors_card_le_divisors_card q (NeZero.ne q)
  have hd : (q : ℝ) ≤ q.divisors.card * (q.totient : ℝ) := by
    exact_mod_cast le_divisors_card_mul_totient q (NeZero.ne q)
  apply (div_le_div_iff₀ hφ hq).mpr
  calc
    _ ≤ (2 * (q.divisors.card : ℝ)) * q := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (by nlinarith) hq.le
    _ ≤ (2 * (q.divisors.card : ℝ)) * (q.divisors.card * (q.totient : ℝ)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

/-- A Haar unit satisfies a prescribed square congruence with probability
at most `2*tau(q)^2/q`. This applies also to inconsistent congruences. -/
theorem unit_square_probability_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    (Nat.card {x : (ZMod q)ˣ // x ^ 2 = a} : ℝ) / Fintype.card (ZMod q)ˣ ≤
      2 * (q.divisors.card : ℝ) ^ 2 / q := by
  rw [ZMod.card_units_eq_totient]
  apply le_trans _ (square_root_density_factor_le q)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast unit_square_fiber_card_le q a

end Ostmann

end OAI
