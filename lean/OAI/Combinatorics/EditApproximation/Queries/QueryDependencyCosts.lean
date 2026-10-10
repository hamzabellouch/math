import OAI.Combinatorics.EditApproximation.Queries.QueryDependencyExpansion
import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoSimulation

namespace OAI

/-! Weighted read counts are the actual same-index and earlier-index
lengths used by the dependency expansion, after identifying its values
with the local mathematical recurrence. -/

namespace EditApproximation

theorem list_filter_length_eq_sum {κ : Type*} (keys : List κ) (predicate : κ → Bool) :
    (keys.filter predicate).length = (keys.map fun key => if predicate key then 1 else 0).sum := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    cases hp : predicate key <;> simp [hp, ih, Nat.add_comm]


section Queries

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery {child : κ // depth child + index child < depth key + index key})
  (expected : κ → ℚ)
  (hstep : ∀ key, (program key).value (fun child => expected child.val) = expected key)

include hstep

theorem queryRequestList_expected (key : κ) :
    queryRequestList depth index program key =
      ((program key).keys (fun child => expected child.val)).map Subtype.val := by
  unfold queryRequestList
  simp only [rankedProgramValue_eq (fun key => depth key + index key) program expected hstep]

theorem querySameRequests_length_eq_cost (key : κ) :
    (querySameRequests depth index program key).length =
      (program key).cost (fun child => expected child.val)
        (fun child => if ¬ index child.val < index key then 1 else 0) := by
  unfold querySameRequests
  rw [queryRequestList_expected depth index program expected hstep,
    list_filter_length_eq_sum, FiniteQuery.cost_eq_sum, List.map_map]
  simp only [Function.comp_def, Bool.not_eq_true', decide_eq_false_iff_not]

theorem queryEarlierRequests_length_eq_cost (key : κ) :
    (queryEarlierRequests depth index program key).length =
      (program key).cost (fun child => expected child.val)
        (fun child => if index child.val < index key then 1 else 0) := by
  unfold queryEarlierRequests
  rw [queryRequestList_expected depth index program expected hstep,
    list_filter_length_eq_sum, FiniteQuery.cost_eq_sum, List.map_map]
  simp only [Function.comp_def, decide_eq_true_eq]

end Queries

end EditApproximation

end OAI
