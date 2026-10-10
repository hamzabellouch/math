import OAI.Combinatorics.EditApproximation.Numerics.RationalWideStep
import OAI.Combinatorics.EditApproximation.Refinement.StageWarmup
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLeaves
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
The complete physical refinement recurrence. Current-index recursive requests
go only to physical children. The selection interface records literal wide
list membership, and carries no approximation or probability assumption.
-/

namespace EditApproximation





structure PhysicalSelections (M J nx ny P : ℕ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval ny)) where
  groups : PhysicalNode M J → PhysicalChildTables M ny → ℕ → List (PhysicalRationalAction M ny)
  online : PhysicalNode M J → PhysicalChildTables M ny → ℕ → TargetInterval ny →
    List (PhysicalRationalAction M ny)
  groups_mem : ∀ node children t action, action ∈ groups node children t →
    action ∈ rationalActualWideActions (physicalSourceInterval nx node) (representatives node) P
  online_mem : ∀ node children t q action, action ∈ online node children t q →
    action ∈ rationalActualWideActions (physicalSourceInterval nx node) (representatives node) P

def physicalRefinement {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) : ℕ → TargetInterval target.length → ℚ :=
  if hbelow : node.1.val < J then
    if (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo ≤ 1 then
      fun _ q => stageInitial source target U N P F A (node, q)
    else
      let children : PhysicalChildTables M target.length := fun i =>
        physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
      fun t q => match t with
        | 0 => stageWarmup source target U N P F A T (node, q)
        | s + 1 => rationalWideStep (physicalSourceInterval source.length node)
            (stageRepresentatives source target U N P F A node) P
            (fun r => stageInitial source target U N P F A (node, r)) (128 * F) delta
            (fun is => children is.1 s is.2) (fun is => children is.1 (s + 1) is.2)
            (choices.groups node children (s + 1)) (choices.online node children (s + 1) q) q
  else fun _ q => stageInitial source target U N P F A (node, q)
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

theorem physicalRefinement_at_leaf {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stateEditCost (physicalSource source node) target q := by
  rw [physicalRefinement]
  have hlength : (physicalSource source node).length ≤ 1 := (physicalSource_length_eq source node).trans_le hleaf
  split_ifs <;>
    simp only [stageInitial, physicalInitialTable, ite_eq_left hlength,
      shortSourceCost_eq_edit _ _ hlength] <;> rfl

theorem physicalRefinement_at_last_level {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hlast : node.1.val = J) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stageInitial source target U N P F A (node, q) := by
  rw [physicalRefinement]
  rw [dite_eq_right (by omega : ¬ node.1.val < J)]

theorem physicalRefinement_succ {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    let children : PhysicalChildTables M target.length := fun i =>
      physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
    physicalRefinement source target U N P F A T delta choices node (t + 1) q =
      rationalWideStep (physicalSourceInterval source.length node)
        (stageRepresentatives source target U N P F A node) P
        (fun r => stageInitial source target U N P F A (node, r)) (128 * F) delta
        (fun is => children is.1 t is.2) (fun is => children is.1 (t + 1) is.2)
        (choices.groups node children (t + 1)) (choices.online node children (t + 1) q) q := by
  rw [physicalRefinement]
  rw [dite_eq_left hbelow, ite_eq_right hleaf]

end EditApproximation

end OAI
