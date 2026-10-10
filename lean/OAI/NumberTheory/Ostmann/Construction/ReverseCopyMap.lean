import OAI.NumberTheory.Ostmann.Construction.SchedulePivotSlots
import OAI.NumberTheory.Ostmann.Construction.WordTransferTemplate

namespace OAI

/-! # Reversing the literal copied-atom schedule

This construction is at the atom level: a current pivot group is one atom
carrying its total product. -/

namespace Ostmann

open scoped Classical

abbrev CopyScheduleAtoms {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i}

/-- The chosen child reads its H copy and the common Y. The erased pivot
is represented by the coordinate that the arithmetic node reconstructs. -/
noncomputable def reverseCopyLabelMap {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (i : CopyScheduleAtoms role n) : σ :=
  if hc : (copyScheduleRole role n i.val).copiedAt n = true then
    current ⟨.inl (b, i.val), i.property, hc⟩
  else if he : (copyScheduleRole role n i.val).erasedAt n = true then pivot
  else current ⟨.inr i.val, i.property, Bool.eq_false_iff.mpr hc, Bool.eq_false_iff.mpr he⟩

theorem reverseCopyLabelMap_copied {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (i : CopyScheduleH role n) :
    reverseCopyLabelMap role n b pivot current ⟨i.val, i.property.1⟩ =
      current ⟨.inl (b, i.val), i.property⟩ := by
  simp only [reverseCopyLabelMap, i.property.2, dite_true]

theorem reverseCopyLabelMap_retained {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (i : CopyScheduleY role n) :
    reverseCopyLabelMap role n b pivot current ⟨i.val, i.property.1⟩ =
      current ⟨.inr i.val, i.property⟩ := by
  simp only [reverseCopyLabelMap, i.property.2.1, Bool.false_eq_true, dite_false, i.property.2.2]

theorem reverseCopyLabelMap_erased {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (i : CopyScheduleAtoms role n) (hi : copyScheduleRole role n i.val = .pivot n) :
    reverseCopyLabelMap role n b pivot current i = pivot := by
  simp [reverseCopyLabelMap, hi, CopyScheduleRole.copiedAt, CopyScheduleRole.erasedAt]

/-- There is exactly one replaced coordinate when the pivot group is
represented by one original atom. This is the manuscript's grouping convention. -/
theorem reverseCopyLabelMap_unique_pivot {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (p : I) (hp : role p = .pivot n) (hunique : ∀ i, role i = .pivot n → i = p) :
    ∃! i : CopyScheduleAtoms role n,
      copyScheduleRole role n i.val = .pivot n ∧ reverseCopyLabelMap role n b pivot current i = pivot := by
  let i : CopyScheduleAtoms role n := ⟨copySchedulePositive n p,
    copyScheduleSurvives_positive role p n hp n le_rfl⟩
  have hi : copyScheduleRole role n i.val = .pivot n := copyScheduleRole_positive role p n hp n
  refine ⟨i, ⟨hi, reverseCopyLabelMap_erased role n b pivot current i hi⟩, ?_⟩
  intro j hj
  apply Subtype.ext
  obtain ⟨_, q, hq, hval⟩ := surviving_pivot_is_positive role n n j.val j.property hj.1
  simpa only [hunique q hq] using hval

end Ostmann

end OAI
