import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementInvariants

namespace OAI

/-!
# Locality of the complete physical refinement

Changing selection streams above a fixed level cannot alter histories at
that level or below. This proves the fixed-child environment under
parent-only resampling directly from the executable recurrence.
-/

namespace EditApproximation

/-- The complete history depends only on selection functions at its own
physical level and deeper levels. -/
theorem physicalRefinement_congr_from_level {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (first second : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (d : ℕ) (hgroups : ∀ node, d ≤ node.1.val → first.groups node = second.groups node)
    (honline : ∀ node, d ≤ node.1.val → first.online node = second.online node)
    (node : PhysicalNode M J) (hnode : d ≤ node.1.val) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta first node t q =
      physicalRefinement source target U N P F A T delta second node t q := by
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_leaf source target U N P F A T delta first node hleaf,
        physicalRefinement_at_leaf source target U N P F A T delta second node hleaf]
    · have hchildren (i : Fin M) :
          physicalRefinement source target U N P F A T delta first (physicalChild node hbelow i) =
            physicalRefinement source target U N P F A T delta second (physicalChild node hbelow i) := by
        funext t q
        exact physicalRefinement_congr_from_level source target U N P F A T delta first second d hgroups honline
          (physicalChild node hbelow i) (by change d ≤ node.1.val + 1; omega) t q
      cases t with
      | zero =>
        rw [physicalRefinement_zero source target U N P F A T delta first,
          physicalRefinement_zero source target U N P F A T delta second]
      | succ t =>
        rw [physicalRefinement_succ source target U N P F A T delta first node hbelow hleaf,
          physicalRefinement_succ source target U N P F A T delta second node hbelow hleaf]
        simp only [hchildren, hgroups node hnode, honline node hnode]
  · have hlast : node.1.val = J := by have hbound := node.1.isLt; omega
    rw [physicalRefinement_at_last_level source target U N P F A T delta first node hlast,
      physicalRefinement_at_last_level source target U N P F A T delta second node hlast]
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

/-- Parent-only resampling fixes every child table, at every refinement
index and target state, without independence assumptions about children. -/
theorem physicalRefinement_children_fixed {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (first second : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hgroups : ∀ label, node.1.val < label.1.val → first.groups label = second.groups label)
    (honline : ∀ label, node.1.val < label.1.val → first.online label = second.online label) :
    (fun i : Fin M => physicalRefinement source target U N P F A T delta first (physicalChild node hbelow i)) =
      fun i : Fin M => physicalRefinement source target U N P F A T delta second (physicalChild node hbelow i) := by
  funext i t q
  apply physicalRefinement_congr_from_level source target U N P F A T delta first second (node.1.val + 1)
  · intro label hlabel
    exact hgroups label (by omega)
  · intro label hlabel
    exact honline label (by omega)
  · change node.1.val + 1 ≤ node.1.val + 1
    rfl

end EditApproximation

end OAI
