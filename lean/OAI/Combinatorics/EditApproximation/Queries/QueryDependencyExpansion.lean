import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoWork
import OAI.Combinatorics.EditApproximation.Geometry.DependencyExpansion

namespace OAI

/-! The dependency tree here is obtained from the requests made by the
finite adaptive program at its actual answers. Local depth/index progress
therefore bounds execution, rather than an independently supplied tree. -/

namespace EditApproximation

open Finset

section Queries

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery
    {child : κ // depth child + index child < depth key + index key})

def queryRequestList (key : κ) : List κ :=
  ((program key).keys (fun child =>
    rankedProgramValue (fun x => depth x + index x) program child.val)).map Subtype.val

def querySameRequests (key : κ) : List κ :=
  (queryRequestList depth index program key).filter (fun child => !(index child < index key))

def queryEarlierRequests (key : κ) : List κ :=
  (queryRequestList depth index program key).filter (fun child => index child < index key)

theorem queryRequestList_cost (key : κ) (weight : κ → ℕ) :
    (program key).cost
        (fun child => rankedProgramValue (fun x => depth x + index x) program child.val)
        (fun child => weight child.val) =
      ((queryRequestList depth index program key).map weight).sum := by
  rw [FiniteQuery.cost_eq_sum]
  simp only [queryRequestList, List.map_map, Function.comp_def]

theorem sum_map_partition (predicate : κ → Bool) (weight : κ → ℕ) (keys : List κ) :
    ((keys.filter (fun key => !predicate key)).map weight).sum +
      ((keys.filter predicate).map weight).sum = (keys.map weight).sum := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    cases hp : predicate key <;> simp only [List.filter_cons, hp, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, reduceIte, List.map_cons, List.sum_cons]
    all_goals omega

variable (progress : ∀ key child, child ∈ queryRequestList depth index program key →
  (depth child < depth key ∧ index child ≤ index key) ∨
  (depth child ≤ depth key ∧ index child < index key))

include progress

theorem querySameRequests_progress (key : κ)
    (i : Fin (querySameRequests depth index program key).length) :
    depth ((querySameRequests depth index program key).get i) < depth key ∧
      index ((querySameRequests depth index program key).get i) ≤ index key := by
  have hm := List.mem_filter.mp (List.get_mem (querySameRequests depth index program key) i)
  have hnot : ¬ index ((querySameRequests depth index program key).get i) < index key := by
    simpa using hm.2
  rcases progress key _ hm.1 with h | h
  · exact h
  · exact False.elim (hnot h.2)

theorem queryEarlierRequests_progress (key : κ)
    (i : Fin (queryEarlierRequests depth index program key).length) :
    depth ((queryEarlierRequests depth index program key).get i) ≤ depth key ∧
      index ((queryEarlierRequests depth index program key).get i) < index key := by
  have hm := List.mem_filter.mp (List.get_mem (queryEarlierRequests depth index program key) i)
  have hi : index ((queryEarlierRequests depth index program key).get i) < index key := by
    simpa only [decide_eq_true_eq] using hm.2
  refine ⟨?_, hi⟩
  rcases progress key _ hm.1 with h | h
  · exact h.1.le
  · exact h.1

def queryDependencyExpansion (root : κ) : DependencyExpansion :=
  DependencyExpansion.build depth index
    (fun key => (querySameRequests depth index program key).length)
    (fun key => (queryEarlierRequests depth index program key).length)
    (fun key i => (querySameRequests depth index program key).get i)
    (fun key i => (queryEarlierRequests depth index program key).get i)
    (querySameRequests_progress depth index program progress)
    (queryEarlierRequests_progress depth index program progress) root

theorem queryDependencyExpansion_depth (root : κ) :
    (queryDependencyExpansion depth index program progress root).depth = depth root :=
  DependencyExpansion.build_depth _ _ _ _ _ _ _ _ root

theorem queryDependencyExpansion_index (root : κ) :
    (queryDependencyExpansion depth index program progress root).rank = index root :=
  DependencyExpansion.build_rank _ _ _ _ _ _ _ _ root

theorem queryDependencyExpansion_valid (a b : ℕ)
    (hsame : ∀ key, (querySameRequests depth index program key).length ≤ a)
    (hearlier : ∀ key, (queryEarlierRequests depth index program key).length ≤ b) (root : κ) :
    DependencyExpansion.Valid a b (queryDependencyExpansion depth index program progress root) :=
  DependencyExpansion.build_valid _ _ _ _ _ _ _ _ a b hsame hearlier root

theorem queryDependencyExpansion_nodes (root : κ) :
    (queryDependencyExpansion depth index program progress root).nodeCount =
      rankedUncachedCalls (fun key => depth key + index key) program root := by
  have hall : ∀ level root, depth root + index root = level →
      (queryDependencyExpansion depth index program progress root).nodeCount =
        rankedUncachedCalls (fun key => depth key + index key) program root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hroot
      conv_lhs => unfold queryDependencyExpansion
      rw [DependencyExpansion.build]
      change 1 + (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).nodeCount) +
        (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).nodeCount) = _
      have hs (i : Fin (querySameRequests depth index program root).length) :=
        querySameRequests_progress depth index program progress root i
      have he (i : Fin (queryEarlierRequests depth index program root).length) :=
        queryEarlierRequests_progress depth index program progress root i
      have hsame : (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).nodeCount) =
        (((querySameRequests depth index program root).map
          (rankedUncachedCalls (fun key => depth key + index key) program)).sum) := by
        calc
          _ = ∑ i : Fin (querySameRequests depth index program root).length,
              rankedUncachedCalls (fun key => depth key + index key) program
                ((querySameRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_lt_of_le (hs i).1 (hs i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      have hearlier : (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).nodeCount) =
        (((queryEarlierRequests depth index program root).map
          (rankedUncachedCalls (fun key => depth key + index key) program)).sum) := by
        calc
          _ = ∑ i : Fin (queryEarlierRequests depth index program root).length,
              rankedUncachedCalls (fun key => depth key + index key) program
                ((queryEarlierRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_le_of_lt (he i).1 (he i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      rw [hsame, hearlier, rankedUncachedCalls, queryRequestList_cost]
      have hp := sum_map_partition (fun child => decide (index child < index root))
        (rankedUncachedCalls (fun key => depth key + index key) program)
        (queryRequestList depth index program root)
      change 1 + _ + _ = _ + 1
      change _ + _ = _ at hp
      dsimp only [querySameRequests, queryEarlierRequests]
      omega
  exact hall (depth root + index root) root rfl

theorem rankedMemoEvaluate_dependency_bound (a b bits : ℕ) (encode : κ → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (hsame : ∀ key, (querySameRequests depth index program key).length ≤ a)
    (hearlier : ∀ key, (queryEarlierRequests depth index program key).length ≤ b) (root : κ) :
    (rankedMemoEvaluate (fun key => depth key + index key) program bits encode root .empty).requests ≤
      dependencyPathBudget (depth root) (index root) a b := by
  calc
    _ ≤ rankedUncachedCalls (fun key => depth key + index key) program root :=
      rankedMemoEvaluate_requests_le _ _ bits encode hinjective hbounded root .empty
        (memoSound_empty bits encode _)
    _ = (queryDependencyExpansion depth index program progress root).nodeCount :=
      (queryDependencyExpansion_nodes depth index program progress root).symm
    _ ≤ dependencyPathBudget (depth root) (index root) a b := by
      simpa only [queryDependencyExpansion_depth, queryDependencyExpansion_index] using
        DependencyExpansion.nodeCount_le_budget a b _
          (queryDependencyExpansion_valid depth index program progress a b hsame hearlier root)

end Queries

end EditApproximation

end OAI
