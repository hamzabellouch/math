import OAI.NumberTheory.Ostmann.Construction.InsertedAtomAssignment

namespace OAI

/-! # Distinct sources in the actual reverse atom substitution -/

namespace Ostmann
open scoped Classical

/-- None is the newly reconstructed pivot. Every other atom reads one
particular copied or retained atom from the parent assignment. -/
noncomputable def reverseAtomSource {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) : CopyScheduleAtoms role n → Option (CopyScheduleAtoms role (n + 1)) :=
  reverseCopyLabelMap role n b none some

theorem reverseAtomSource_pivot {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (p : CurrentPivotConstituent role n) :
    reverseAtomSource role n b (scheduledPartitionEquiv role n (.inl p)) = none :=
  reverseCopyLabelMap_erased role n b none some _
    (copyScheduleRole_positive role p.val n p.property n)

theorem reverseAtomSource_H {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (h : CopyScheduleH role n) :
    reverseAtomSource role n b (scheduledPartitionEquiv role n (.inr (.inl h))) =
      some ⟨.inl (b, h.val), h.property⟩ :=
  reverseCopyLabelMap_copied role n b none some h

theorem reverseAtomSource_Y {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (y : CopyScheduleY role n) :
    reverseAtomSource role n b (scheduledPartitionEquiv role n (.inr (.inr y))) =
      some ⟨.inr y.val, y.property⟩ :=
  reverseCopyLabelMap_retained role n b none some y

/-- A unique pivot atom prevents any duplication in a reverse substitution.
In particular each previously inserted pivot occurs at most once in a branch. -/
theorem reverseAtomSource_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool)
    (hu : ∀ i j, role i = .pivot n → role j = .pivot n → i = j) :
    Function.Injective (reverseAtomSource role n b) := by
  intro v w hvw
  obtain ⟨v, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  obtain ⟨w, rfl⟩ := (scheduledPartitionEquiv role n).surjective w
  rcases v with p | h | y <;> rcases w with q | h' | y'
  · congr 2
    exact Subtype.ext (hu p.val q.val p.property q.property)
  · rw [reverseAtomSource_pivot, reverseAtomSource_H] at hvw
    cases hvw
  · rw [reverseAtomSource_pivot, reverseAtomSource_Y] at hvw
    cases hvw
  · rw [reverseAtomSource_H, reverseAtomSource_pivot] at hvw
    cases hvw
  · rw [reverseAtomSource_H, reverseAtomSource_H] at hvw
    have he : h = h' := Subtype.ext (congrArg Prod.snd
      (Sum.inl.inj (congrArg Subtype.val (Option.some.inj hvw))))
    rw [he]
  · rw [reverseAtomSource_H, reverseAtomSource_Y] at hvw
    have he := congrArg Subtype.val (Option.some.inj hvw)
    cases he
  · rw [reverseAtomSource_Y, reverseAtomSource_pivot] at hvw
    cases hvw
  · rw [reverseAtomSource_Y, reverseAtomSource_H] at hvw
    have he := congrArg Subtype.val (Option.some.inj hvw)
    cases he
  · rw [reverseAtomSource_Y, reverseAtomSource_Y] at hvw
    have he : y = y' := Subtype.ext (Sum.inr.inj (congrArg Subtype.val (Option.some.inj hvw)))
    rw [he]

theorem reverseCopyLabelMap_source {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (P : A) (x : CopyScheduleAtoms role (n + 1) → A)
    (v : CopyScheduleAtoms role n) :
    reverseCopyLabelMap role n b P x v = (reverseAtomSource role n b v).elim P x := by
  unfold reverseAtomSource reverseCopyLabelMap
  split_ifs <;> rfl

theorem reverseCopyLabelMap_injective {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool)
    (hu : ∀ i j, role i = .pivot n → role j = .pivot n → i = j)
    (P : A) (current : CopyScheduleAtoms role (n + 1) → A)
    (hc : Function.Injective current) (hP : ∀ v, current v ≠ P) :
    Function.Injective (reverseCopyLabelMap role n b P current) := by
  have hmap : Function.Injective (fun z : Option (CopyScheduleAtoms role (n + 1)) => z.elim P current) := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (hP b h.symm)
    | some a =>
      cases b with
      | none => exact False.elim (hP a h)
      | some b => exact congrArg some (hc h)
  intro v w h
  apply reverseAtomSource_injective role n b hu
  apply hmap
  simpa only [← reverseCopyLabelMap_source] using h

end Ostmann

end OAI
