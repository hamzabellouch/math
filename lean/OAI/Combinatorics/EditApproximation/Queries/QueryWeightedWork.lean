import OAI.Combinatorics.EditApproximation.Queries.QueryDependencyExpansion

namespace OAI

/-! Per-request local work summed along the actual adaptive expansion.
This is a weighted analogue of the uncached request count. -/

namespace EditApproximation

open Finset

def rankedUncachedWork {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (weight : κ → ℕ) (key : κ) : ℕ :=
  (program key).cost (fun child => rankedProgramValue rank program child.val)
    (fun child => rankedUncachedWork rank program weight child.val) + weight key
termination_by rank key
decreasing_by exact child.property

section Weighted

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery
    {child : κ // depth child + index child < depth key + index key})
  (progress : ∀ key child, child ∈ queryRequestList depth index program key →
    (depth child < depth key ∧ index child ≤ index key) ∨
    (depth child ≤ depth key ∧ index child < index key))

theorem queryDependencyExpansion_weighted (weight : ℕ → ℕ) (root : κ) :
    (queryDependencyExpansion depth index program progress root).depthWeightedCount weight =
      rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)) root := by
  have hall : ∀ level root, depth root + index root = level →
      (queryDependencyExpansion depth index program progress root).depthWeightedCount weight =
        rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hroot
      conv_lhs => unfold queryDependencyExpansion
      rw [DependencyExpansion.build]
      change weight (depth root) + (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).depthWeightedCount weight) +
        (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).depthWeightedCount weight) = _
      have hs (i : Fin (querySameRequests depth index program root).length) :=
        querySameRequests_progress depth index program progress root i
      have he (i : Fin (queryEarlierRequests depth index program root).length) :=
        queryEarlierRequests_progress depth index program progress root i
      have hsame : (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).depthWeightedCount weight) =
        (((querySameRequests depth index program root).map
          (rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)))).sum) := by
        calc
          _ = ∑ i : Fin (querySameRequests depth index program root).length,
              rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key))
                ((querySameRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_lt_of_le (hs i).1 (hs i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      have hearlier : (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).depthWeightedCount weight) =
        (((queryEarlierRequests depth index program root).map
          (rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)))).sum) := by
        calc
          _ = ∑ i : Fin (queryEarlierRequests depth index program root).length,
              rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key))
                ((queryEarlierRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_le_of_lt (he i).1 (he i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      rw [hsame, hearlier, rankedUncachedWork, queryRequestList_cost]
      have hp := sum_map_partition (fun child => decide (index child < index root))
        (rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)))
        (queryRequestList depth index program root)
      change weight (depth root) + _ + _ = _ + weight (depth root)
      change _ + _ = _ at hp
      dsimp only [querySameRequests, queryEarlierRequests]
      omega
  exact hall (depth root + index root) root rfl

end Weighted

end EditApproximation

end OAI
