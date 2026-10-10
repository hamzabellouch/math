import OAI.Analysis.Nonexpansive.CandidateSelection
import OAI.Analysis.Nonexpansive.FrontierFromGroups

namespace OAI

/-!
# A concrete sequential construction of one finite level

Parents are visited in their finite order.  Each adaptive return starts
from the full final history of the preceding parent.  The retained
positive children are then concatenated into an actual frontier extension.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints.CandidateContext

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {D : NormalizedMinimalData (X := X)} (C : CandidateContext D)

/-- A total parent index for the natural-number recursion.  Only the first
`frontier.size` stages are used to construct the finite level. -/
def parentAt (i : ℕ) : Fin C.frontier.size :=
  ⟨i % C.frontier.size, Nat.mod_lt i C.frontier.size_pos⟩

@[simp] theorem parentAt_fin (p : Fin C.frontier.size) : C.parentAt p.val = p := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt p.isLt

variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (hanchor : C.anchor = A.x) {τ : ℝ} (hτ : 0 < τ)

/-- Successive parents share the complete chronological candidate history. -/
def levelStates : ℕ → C.State
  | 0 => HistoryState.empty
  | i + 1 =>
    let r := C.selectParent A hanchor (C.parentAt i)
      (levelStates i) hτ
    r.state (Fin.last r.N)

@[simp] theorem levelStates_zero :
    C.levelStates A hanchor hτ 0 = HistoryState.empty := rfl

theorem levelStates_succ (i : ℕ) :
    C.levelStates A hanchor hτ (i + 1) =
      let r := C.selectParent A hanchor (C.parentAt i)
        (C.levelStates A hanchor hτ i) hτ
      r.state (Fin.last r.N) := rfl

/-- The actual return chosen while processing this parent. -/
def group (p : Fin C.frontier.size) :
    C.ParentReturn (C.parentAt p.val) (C.levelStates A hanchor hτ p.val) τ :=
  C.selectParent A hanchor (C.parentAt p.val) (C.levelStates A hanchor hτ p.val) hτ

/-- The entire final state of a parent's return starts the next stage. -/
theorem group_finalState (p : Fin C.frontier.size) :
    (C.group A hanchor hτ p).state (Fin.last (C.group A hanchor hτ p).N) =
      C.levelStates A hanchor hτ (p.val + 1) := rfl

/-- Each retained child is the actual tail map selected by its parent's sequence. -/
theorem group_map_generated (p : Fin C.frontier.size)
    (j : Fin (C.group A hanchor hτ p).q) :
    Generated D.closed D.convex D.T D.nonexpansive
      ((C.group A hanchor hτ p).selected ((C.group A hanchor hτ p).retain j)) :=
  tailFamily_generated D.closed D.convex D.T D.nonexpansive
    ((C.group A hanchor hτ p).legal ((C.group A hanchor hτ p).retain j)).1

theorem group_map_nonexpansive (p : Fin C.frontier.size)
    (j : Fin (C.group A hanchor hτ p).q) :
    LipschitzWith 1
      ((C.group A hanchor hτ p).selected ((C.group A hanchor hτ p).retain j)) :=
  tailFamily_nonexpansive D.closed D.convex D.T D.nonexpansive
    ((C.group A hanchor hτ p).legal ((C.group A hanchor hτ p).retain j)).1

/-- Assemble the retained positive children, in their original parent order. -/
def levelExtension : FrontierExtension C.frontier :=
  FrontierExtension.ofGroups C.frontier
    (fun p => (C.group A hanchor hτ p).q)
    (fun p => (C.group A hanchor hτ p).q_pos)
    (fun p j => (C.group A hanchor hτ p).β ((C.group A hanchor hτ p).retain j))
    (fun p j => (C.group A hanchor hτ p).retained_pos j)
    (fun p => (C.group A hanchor hτ p).retained_sum)
    (fun p j => (C.group A hanchor hτ p).selected ((C.group A hanchor hτ p).retain j))
    (C.group_map_nonexpansive A hanchor hτ)

@[simp] theorem levelExtension_size :
    (C.levelExtension A hanchor hτ).size =
      OrderedGroupConcat.total (fun p => (C.group A hanchor hτ p).q) := rfl

@[simp] theorem levelExtension_parent_group (p : Fin C.frontier.size)
    (j : Fin (C.group A hanchor hτ p).q) :
    (C.levelExtension A hanchor hτ).parent
      (OrderedGroupConcat.group (fun p => (C.group A hanchor hτ p).q) p j) = p :=
  OrderedGroupConcat.parent_group (fun p => (C.group A hanchor hτ p).q) p j

@[simp] theorem levelExtension_weight_group (p : Fin C.frontier.size)
    (j : Fin (C.group A hanchor hτ p).q) :
    (C.levelExtension A hanchor hτ).weight
      (OrderedGroupConcat.group (fun p => (C.group A hanchor hτ p).q) p j) =
      (C.group A hanchor hτ p).β ((C.group A hanchor hτ p).retain j) := by
  unfold levelExtension
  exact FrontierExtension.ofGroups_weight_group C.frontier
    (fun p => (C.group A hanchor hτ p).q)
    (fun p => (C.group A hanchor hτ p).q_pos)
    (fun p j => (C.group A hanchor hτ p).β ((C.group A hanchor hτ p).retain j))
    (fun p j => (C.group A hanchor hτ p).retained_pos j)
    (fun p => (C.group A hanchor hτ p).retained_sum)
    (fun p j => (C.group A hanchor hτ p).selected ((C.group A hanchor hτ p).retain j))
    (C.group_map_nonexpansive A hanchor hτ) p j

@[simp] theorem levelExtension_map_group (p : Fin C.frontier.size)
    (j : Fin (C.group A hanchor hτ p).q) :
    (C.levelExtension A hanchor hτ).map
      (OrderedGroupConcat.group (fun p => (C.group A hanchor hτ p).q) p j) =
      (C.group A hanchor hτ p).selected ((C.group A hanchor hτ p).retain j) := by
  unfold levelExtension
  exact FrontierExtension.ofGroups_map_group C.frontier
    (fun p => (C.group A hanchor hτ p).q)
    (fun p => (C.group A hanchor hτ p).q_pos)
    (fun p j => (C.group A hanchor hτ p).β ((C.group A hanchor hτ p).retain j))
    (fun p j => (C.group A hanchor hτ p).retained_pos j)
    (fun p => (C.group A hanchor hτ p).retained_sum)
    (fun p j => (C.group A hanchor hτ p).selected ((C.group A hanchor hτ p).retain j))
    (C.group_map_nonexpansive A hanchor hτ) p j

/-- Every map in the assembled extension has its actual generation proof. -/
theorem levelExtension_generated (i : Fin (C.levelExtension A hanchor hτ).size) :
    Generated D.closed D.convex D.T D.nonexpansive
      ((C.levelExtension A hanchor hτ).map i) := by
  let s : OrderedGroupConcat.Index (fun p => (C.group A hanchor hτ p).q) :=
    (OrderedGroupConcat.equiv (fun p => (C.group A hanchor hτ p).q)).symm i
  exact C.group_map_generated A hanchor hτ s.1 s.2

/-- The actual child averages return to the anchor with the chosen tolerance. -/
theorem levelExtension_childAverage_near (p : Fin C.frontier.size) :
    ‖((C.levelExtension A hanchor hτ).childAverage
      (fun i => (C.levelExtension A hanchor hτ).map i C.anchor) p : X) -
      (C.anchor : X)‖ < τ := by
  unfold levelExtension
  apply FrontierExtension.ofGroups_childAverage_near
  intro p
  exact (C.group A hanchor hτ p).retained_near

/-- The history after precisely one pass through all current parents. -/
def finalState : C.State := C.levelStates A hanchor hτ C.frontier.size

end ReflexiveFixedPoints.CandidateContext

end

end OAI
