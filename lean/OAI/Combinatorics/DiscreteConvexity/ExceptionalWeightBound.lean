import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Field.Basic

namespace OAI

/-!
# An exceptional-weight lower bound from a signed identity

Separating the empty subset in a vanishing signed sum bounds its weight by
the total unsigned weight of the nonempty subsets. This scalar argument does
not depend on how the weights or their signed identity were constructed.
-/

namespace TalagrandDiscreteConvexity

open scoped BigOperators

/-- A vanishing signed 32nd-power sum and an empty-subset value at least one
half force a lower bound on the sum of the nonempty squared weights. -/
theorem exceptional_lower_bound_of_signed_sum {V : Type*} [DecidableEq V]
    (S : Finset V) (b : Finset V → ℝ)
    (hsum : ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b U ^ 32 = 0)
    (hb0 : (1 / 2 : ℝ) ≤ b ∅) :
    (1 / 2 : ℝ) ^ 32 ≤ ∑ U ∈ S.powerset.erase ∅, (b U ^ 2) ^ 16 := by
  have hpower (U : Finset V) : b U ^ 32 = (b U ^ 2) ^ 16 := by
    rw [← pow_mul]
  have hnonneg (U : Finset V) : 0 ≤ b U ^ 32 := by
    rw [hpower]
    exact pow_nonneg (sq_nonneg (b U)) 16
  have hsplit :
      (∑ U ∈ S.powerset.erase ∅, (-1 : ℝ) ^ U.card * b U ^ 32) +
        b ∅ ^ 32 = 0 := by
    simpa only [Finset.card_empty, pow_zero, one_mul] using
      (Finset.sum_erase_add S.powerset
        (fun U => (-1 : ℝ) ^ U.card * b U ^ 32)
        (Finset.empty_mem_powerset S)).trans hsum
  have hrest :
      (∑ U ∈ S.powerset.erase ∅, (-1 : ℝ) ^ U.card * b U ^ 32) =
        -(b ∅ ^ 32) := eq_neg_of_add_eq_zero_left hsplit
  calc
    (1 / 2 : ℝ) ^ 32 ≤ b ∅ ^ 32 :=
      pow_le_pow_left₀ (div_nonneg zero_le_one zero_le_two) hb0 32
    _ = |∑ U ∈ S.powerset.erase ∅, (-1 : ℝ) ^ U.card * b U ^ 32| := by
      rw [hrest, abs_neg, abs_of_nonneg (hnonneg ∅)]
    _ ≤ ∑ U ∈ S.powerset.erase ∅, |(-1 : ℝ) ^ U.card * b U ^ 32| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ U ∈ S.powerset.erase ∅, (b U ^ 2) ^ 16 := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (hnonneg U), hpower]

end TalagrandDiscreteConvexity

end OAI
