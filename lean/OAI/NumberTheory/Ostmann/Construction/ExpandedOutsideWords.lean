import OAI.NumberTheory.Ostmann.Construction.ExpandedOutsideCoordinates
import OAI.NumberTheory.Ostmann.Construction.ScheduleAtomSystem

namespace OAI

/-! # The original prime constituents of each retained Y atom -/

namespace Ostmann

open scoped Classical

def expandedOriginalWord {V : Type*} {depth : ℕ} :
    List (ExpandedScheduledVariable V depth) → List V
  | [] => []
  | .inl v :: w => v :: expandedOriginalWord w
  | .inr _ :: w => expandedOriginalWord w

theorem expandedOriginalWord_length {V : Type*} {depth : ℕ}
    (w : List (ExpandedScheduledVariable V depth)) :
    (expandedOriginalWord w).length ≤ w.length := by
  induction w with
  | nil => rfl
  | cons v w ih => cases v <;> simp only [expandedOriginalWord, List.length_cons] <;> omega

theorem expandedOriginalWord_exact {V : Type*} {depth : ℕ}
    (w : List (ExpandedScheduledVariable V depth))
    (hw : ∀ v ∈ w, ∃ a : V, v = .inl a) :
    (expandedOriginalWord w).map Sum.inl = w := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    obtain ⟨a, rfl⟩ := hw v (by simp)
    simp only [expandedOriginalWord, List.map_cons]
    rw [ih (fun v hv => hw v (by simp only [List.mem_cons]; exact Or.inr hv))]

theorem expandedOriginalWord_values {V : Type*} {depth : ℕ} {β : Type*}
    (w : List (ExpandedScheduledVariable V depth))
    (hw : ∀ v ∈ w, ∃ a : V, v = .inl a)
    (x : ExpandedScheduledVariable V depth → β) :
    (expandedOriginalWord w).map (fun a => x (.inl a)) = w.map x := by
  calc
    _ = ((expandedOriginalWord w).map Sum.inl).map x := (List.map_map ..).symm
    _ = _ := congrArg (List.map x) (expandedOriginalWord_exact w hw)

def expandedYPrimeWord {I V : Type*} (role : I → CopyScheduleRole) (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (i : CopyScheduleY role n) : List V :=
  expandedOriginalWord (current ⟨.inr i.val, i.property⟩)

theorem expandedYPrimeWord_values {I V β : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current)
    (i : CopyScheduleY role n) (x : ExpandedScheduledVariable V depth → β) :
    (expandedYPrimeWord role depth n current i).map (fun a => x (.inl a)) =
      (current ⟨.inr i.val, i.property⟩).map x :=
  expandedOriginalWord_values _ (expandedYWord_actual role depth n current hc i) x

theorem expandedYPrimeWord_product {I V : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current)
    (i : CopyScheduleY role n) (x : ExpandedScheduledVariable V depth → ℕ) :
    ((expandedYPrimeWord role depth n current i).map (fun a => x (.inl a))).prod =
      expandedAtomValues role (n + 1) current x ⟨.inr i.val, i.property⟩ := by
  rw [expandedYPrimeWord_values role depth n current hc i x]
  rfl

end Ostmann

end OAI
