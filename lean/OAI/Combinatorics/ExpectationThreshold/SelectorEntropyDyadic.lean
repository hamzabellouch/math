import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Finite dyadic mass for the selector entropy estimate

The positive dyadic levels have total mass at most one, including when there
are no levels.
-/

open scoped BigOperators

namespace TalagrandThreshold

private lemma selector_dyadic_range_sum (s : ℕ) :
    (∑ i ∈ Finset.range s, (1 / 2 : ℝ) ^ (i + 1)) = 1 - (1 / 2 : ℝ) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [pow_succ]
    ring

/-- The dyadic weights of all positive selector levels sum to at most one. -/
theorem selector_dyadic_sum_le_one (s : ℕ) :
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) ≤ 1 := by
  calc
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) =
        ∑ i ∈ Finset.range s, (1 / 2 : ℝ) ^ (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1)) s
    _ = 1 - (1 / 2 : ℝ) ^ s := selector_dyadic_range_sum s
    _ ≤ 1 := sub_le_self _ (pow_nonneg (by norm_num) s)

end TalagrandThreshold

end OAI
