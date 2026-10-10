import Mathlib.Analysis.SpecificLimits.Normed
import OAI.NumberTheory.Ostmann.Arithmetic.SquareRootProbability

namespace OAI

/-! # The elementary divisor bound needed for the frequency moduli

For every fixed power `k`, the `k`th power of the divisor count is bounded
by a constant times `n`. The constant is independent of the modulus.
-/

namespace Ostmann

open scoped BigOperators Classical
open Filter

private theorem successor_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ]
    omega

theorem exists_successor_power_bound (k : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ e : ℕ, (e + 1) ^ k ≤ C * 2 ^ e := by
  have he := (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N ^ k + 2, by omega, fun e => ?_⟩
  by_cases hn : N ≤ e + 1
  · have hpow : ((e + 1 : ℕ) : ℝ) ^ k < (2 : ℝ) ^ (e + 1) :=
      (div_lt_one (by positivity)).mp (hN (e + 1) hn)
    have hnat : (e + 1) ^ k ≤ 2 ^ (e + 1) := by exact_mod_cast hpow.le
    rw [pow_succ] at hnat
    exact hnat.trans (by simpa only [Nat.mul_comm] using
      Nat.mul_le_mul_right (2 ^ e) (show 2 ≤ N ^ k + 2 by omega))
  · have hsmall : (e + 1) ^ k ≤ N ^ k := Nat.pow_le_pow_left (by omega) k
    have ht : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    exact hsmall.trans ((Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one ht)).trans
      (Nat.mul_le_mul_right _ (show N ^ k ≤ N ^ k + 2 by omega)))

private theorem prime_power_divisor_budget (k C p e : ℕ)
    (hbound : ∀ e : ℕ, (e + 1) ^ k ≤ C * 2 ^ e) (hp : p.Prime) :
    (e + 1) ^ k ≤ (if p < 2 ^ k then C else 1) * p ^ e := by
  by_cases hsmall : p < 2 ^ k
  · rw [ite_eq_left hsmall]
    exact (hbound e).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hp.two_le e))
  · rw [ite_eq_right hsmall, one_mul]
    calc
      _ ≤ (2 ^ e) ^ k := Nat.pow_le_pow_left (successor_le_two_pow e) k
      _ = (2 ^ k) ^ e := by rw [← pow_mul, Nat.mul_comm e k, pow_mul]
      _ ≤ p ^ e := Nat.pow_le_pow_left (by omega) e

/-- A concrete power version of `tau(n) = n^o(1)`, proved by separating
the finitely many primes below `2^k` in the factorization. -/
theorem exists_divisors_power_bound (k : ℕ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ n : ℕ, n ≠ 0 → n.divisors.card ^ k ≤ D * n := by
  obtain ⟨C, hC, hbound⟩ := exists_successor_power_bound k
  refine ⟨C ^ (2 ^ k), Nat.one_le_pow _ _ hC, fun n hn => ?_⟩
  have hsmall : (n.primeFactors.filter fun p => p < 2 ^ k).card ≤ 2 ^ k := by
    calc
      _ ≤ (Finset.range (2 ^ k)).card := Finset.card_le_card fun p hp =>
        Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = _ := Finset.card_range _
  have hcost : (∏ p ∈ n.primeFactors, if p < 2 ^ k then C else 1) ≤ C ^ (2 ^ k) := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const]
    exact Nat.pow_le_pow_right hC hsmall
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < 2 ^ k then C else 1) * p ^ n.factorization p := by
      apply Finset.prod_le_prod
      intro p hp
      exact prime_power_divisor_budget k C p (n.factorization p) hbound
        (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, if p < 2 ^ k then C else 1) * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ _ := Nat.mul_le_mul_right n hcost

end Ostmann

end OAI
