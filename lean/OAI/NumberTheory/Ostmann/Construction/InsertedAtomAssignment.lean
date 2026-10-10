import OAI.NumberTheory.Ostmann.Construction.CopiedPriorFubini
import OAI.NumberTheory.Ostmann.Construction.ReverseCopyMap

namespace OAI

/-! # Inserting the reconstructed composite pivot in either old branch -/

namespace Ostmann

open scoped Classical

noncomputable def scheduledInsertedAtoms {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (P : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ) :
    CopyScheduleAtoms role n → ℕ :=
  fun i => match (scheduledPartitionEquiv role n).symm i with
    | .inl _ => P
    | .inr (.inl h) => l h
    | .inr (.inr y) => u y

theorem scheduledInsertedAtoms_pivot {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (P : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (p : CurrentPivotConstituent role n) :
    scheduledInsertedAtoms role n P l u (scheduledPartitionEquiv role n (.inl p)) = P := by
  simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]

theorem scheduledInsertedAtoms_H {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (P : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (h : CopyScheduleH role n) :
    scheduledInsertedAtoms role n P l u ⟨h.val, h.property.1⟩ = l h := by
  change scheduledInsertedAtoms role n P l u (scheduledPartitionEquiv role n (.inr (.inl h))) = _
  simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]

theorem scheduledInsertedAtoms_Y {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (P : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (y : CopyScheduleY role n) :
    scheduledInsertedAtoms role n P l u ⟨y.val, y.property.1⟩ = u y := by
  change scheduledInsertedAtoms role n P l u (scheduledPartitionEquiv role n (.inr (.inr y))) = _
  simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]

/-- The arithmetic reverse substitution uses precisely the old H branch,
the single common outside assignment, and the forced composite pivot. -/
theorem reverseCopiedAtoms_eq_inserted {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (P : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ) :
    reverseCopyLabelMap role n b P (scheduledCopiedAssignment role n u l r) =
      scheduledInsertedAtoms role n P (if b then l else r) u := by
  funext i
  obtain ⟨j, rfl⟩ := (scheduledPartitionEquiv role n).surjective i
  rcases j with p | h | y
  · rw [reverseCopyLabelMap_erased role n b P _ _
      (copyScheduleRole_positive role p.val n p.property n), scheduledInsertedAtoms_pivot]
  · change reverseCopyLabelMap role n b P _ ⟨h.val, h.property.1⟩ = _
    apply (reverseCopyLabelMap_copied role n b P _ h).trans
    apply Eq.trans (show scheduledCopiedAssignment role n u l r
        (scheduledOutputVertex role n (.inl (b, h))) = (if b then l else r) h from ?_)
      (scheduledInsertedAtoms_H role n P (if b then l else r) u h).symm
    cases b
    · exact scheduledCopiedAssignment_right role n u l r h
    · exact scheduledCopiedAssignment_left role n u l r h
  · change reverseCopyLabelMap role n b P _ ⟨y.val, y.property.1⟩ = _
    exact (reverseCopyLabelMap_retained role n b P _ y).trans
      ((scheduledCopiedAssignment_outside role n u l r y).trans
        (scheduledInsertedAtoms_Y role n P (if b then l else r) u y).symm)

end Ostmann

end OAI
