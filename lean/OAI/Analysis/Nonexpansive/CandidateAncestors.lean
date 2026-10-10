import OAI.Analysis.Nonexpansive.CandidateStages
import OAI.Analysis.Nonexpansive.BlockBefore
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-!
# The stored ancestor lists are the actual paths of the constructed tree

The stage recursion appends the current parent's map to its stored strict
ancestor list. This is exactly the recursion defining `pathDisplacement`.
The finite sums used when selecting candidates therefore bound the final
tree's actual proper-ancestor displacement.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace CandidateContext

variable {D : NormalizedMinimalData (X := X)} (C : CandidateContext D)

/-- Reading a stored ancestor list by finite indices gives its literal list sum. -/
theorem ancestorMap_sum_eq_list (p : Fin C.frontier.size) (z : D.K) :
    (∑ i : Fin (C.ancestors p).length, ‖(C.ancestorMap p i z : X) - z‖) =
      ((C.ancestors p).map (fun g => ‖(g.val z : X) - z‖)).sum := by
  simpa only [ancestorMap, List.get_eq_getElem] using
    Fin.sum_univ_fun_getElem (C.ancestors p) (fun g => ‖(g.val z : X) - z‖)

theorem candidateAncestorMap_sum_eq_list (p : Fin C.frontier.size) (z : D.K) :
    (∑ i : Fin (C.candidateAncestors p).length,
      ‖(C.candidateAncestorMap p i z : X) - z‖) =
      ((C.candidateAncestors p).map (fun g => ‖(g.val z : X) - z‖)).sum := by
  simpa only [candidateAncestorMap, List.get_eq_getElem] using
    Fin.sum_univ_fun_getElem (C.candidateAncestors p) (fun g => ‖(g.val z : X) - z‖)

/-- A new child's proper ancestors include its current parent's map. -/
theorem candidateAncestorMap_sum_eq (p : Fin C.frontier.size) (z : D.K) :
    (∑ i : Fin (C.candidateAncestors p).length,
      ‖(C.candidateAncestorMap p i z : X) - z‖) =
      (∑ i : Fin (C.ancestors p).length, ‖(C.ancestorMap p i z : X) - z‖) +
        ‖(C.frontier.map p z : X) - z‖ := by
  rw [C.candidateAncestorMap_sum_eq_list, C.ancestorMap_sum_eq_list]
  simp only [candidateAncestors, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]

end CandidateContext

namespace AnchoredCandidateContext

variable (D : NormalizedMinimalData (X := X))
variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (U : Ultrafilter ℕ)

/-- The actual successor list appends the final tree's current parent map. -/
theorem context_ancestors_succ (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    (context D A U (k + 1)).ancestors v =
      (context D A U k).candidateAncestors ((tower D A U).toOrderedTree.parent k v) := rfl

/-- List recursion and actual path recursion compute the same displacement. -/
theorem ancestorList_displacement_eq (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node k) (z : D.K) :
    (((context D A U k).ancestors v).map (fun g => ‖(g.val z : X) - z‖)).sum =
      (tower D A U).toEvaluation.pathDisplacement k v z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      let p : Fin (context D A U k).frontier.size :=
        (tower D A U).toOrderedTree.parent k v
      change
        (((context D A U k).ancestors p ++
          [(⟨(context D A U k).frontier.map p,
            (context D A U k).frontier_generated p⟩ : GeneratedSelfMap D)]).map
          (fun g : GeneratedSelfMap D => ‖(g.val z : X) - z‖)).sum =
        (tower D A U).toEvaluation.pathDisplacement k p z +
          ‖((context D A U k).frontier.map p z : X) - z‖
      simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      exact congrArg
        (fun r : ℝ => r + ‖((context D A U k).frontier.map p z : X) - z‖)
        (ih p)

/-- The exact finite sum over stored strict ancestors equals the final path sum. -/
theorem ancestorMap_sum_eq_pathDisplacement (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node k) (z : D.K) :
    (∑ i : Fin ((context D A U k).ancestors v).length,
      ‖((context D A U k).ancestorMap v i z : X) - z‖) =
      (tower D A U).toEvaluation.pathDisplacement k v z := by
  let p : Fin (context D A U k).frontier.size := v
  exact ((context D A U k).ancestorMap_sum_eq_list p z).trans
    (ancestorList_displacement_eq D A U k v z)

/-- The candidate-selection ancestor sum is exactly the path sum of its new child. -/
theorem candidateAncestorMap_sum_eq_pathDisplacement (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) (z : D.K) :
    (∑ i : Fin ((context D A U k).candidateAncestors
        ((tower D A U).toOrderedTree.parent k v)).length,
      ‖((context D A U k).candidateAncestorMap
        ((tower D A U).toOrderedTree.parent k v) i z : X) - z‖) =
      (tower D A U).toEvaluation.pathDisplacement (k + 1) v z := by
  let p : Fin (context D A U k).frontier.size :=
    (tower D A U).toOrderedTree.parent k v
  exact ((context D A U k).candidateAncestorMap_sum_eq_list p z).trans
    ((congrArg (fun gs : List (GeneratedSelfMap D) =>
        (gs.map (fun g => ‖(g.val z : X) - z‖)).sum)
      (context_ancestors_succ D A U k v).symm).trans
      (ancestorList_displacement_eq D A U (k + 1) v z))

end AnchoredCandidateContext
end ReflexiveFixedPoints

end

end OAI
