import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

namespace OAI

/-!
# Counting bounded-size subsets

Subsets of cardinality at most `r` are counted by a partial binomial sum.
The elementary bound by `(1 + B.card)^r` includes `r = 0` and empty `B`.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

/-- Partition the subsets of `B` of size at most `r` by their cardinality. -/
theorem card_subsets_card_le {V : Type*} [DecidableEq V] (B : Finset V) (r : ℕ) :
    (B.powerset.filter (fun I => I.card ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose B.card i := by
  simpa only [Finset.mem_range, Nat.lt_succ_iff,
    ← Finset.powersetCard_eq_filter, Finset.card_powersetCard] using
    (Finset.sum_card_fiberwise_eq_card_filter B.powerset
      (Finset.range (r + 1)) Finset.card).symm

/-- A partial binomial sum is bounded by the number of length-`r` words
over an alphabet with `n + 1` letters. -/
theorem sum_choose_range_le_pow (n r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), Nat.choose n i) ≤ (1 + n) ^ r := by
  calc
    (∑ i ∈ Finset.range (r + 1), Nat.choose n i)
        ≤ ∑ i ∈ Finset.range (r + 1), n ^ i * Nat.choose r i := by
      apply Finset.sum_le_sum
      intro i hi
      have hc : 1 ≤ Nat.choose r i :=
        Nat.choose_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      exact (Nat.choose_le_pow n i).trans (by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n ^ i) hc)
    _ = (n + 1) ^ r := by
      simpa using (add_pow n 1 r).symm
    _ = (1 + n) ^ r := by rw [Nat.add_comm]

/-- The number of subsets of `B` of size at most `r` is at most `(1 + B.card)^r`. -/
theorem card_subsets_card_le_pow {V : Type*} [DecidableEq V]
    (B : Finset V) (r : ℕ) :
    (B.powerset.filter (fun I => I.card ≤ r)).card ≤ (1 + B.card) ^ r := by
  rw [card_subsets_card_le]
  exact sum_choose_range_le_pow B.card r

end TalagrandDiscreteConvexity.Covering

end OAI
