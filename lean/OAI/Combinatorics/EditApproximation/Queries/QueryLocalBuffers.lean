import OAI.Combinatorics.EditApproximation.Queries.QueryDataBuffers
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Finite reader budgets for the executable adaptive program. These
uniform bounds follow from stored-key widths, regardless of answer values. -/

namespace EditApproximation.BinaryFraction



theorem queryChildReadWithWork_budget {M n : ℕ} (keys : List (Fin M × TargetInterval n))
    (words : List BinaryFraction) (i : Fin M) (r : TargetInterval n) :
    (queryChildReadWithWork keys words i r).2 ≤ queryDataReadBudget M n keys := by
  exact queryChildReadWithWork_cost keys words i r _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)



@[simp] theorem queryParentReadWithWork_value {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    (queryParentReadWithWork keys words r).1.value = finiteAnswerTable keys (words.map value) r :=
  gatheredWordLookupWithWork_value _ queryIntervalEqualWithWork_value keys words r

theorem queryParentReadWithWork_cost {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    (queryParentReadWithWork keys words r).2 ≤ 1 + keys.length * (16 * Nat.size n + 6) := by
  exact gatheredWordLookupWithWork_cost queryIntervalEqualWithWork (16 * Nat.size n + 5)
    (fun a b => queryIntervalEqualWithWork_cost a b _ le_rfl) keys words r

end EditApproximation.BinaryFraction

end OAI
