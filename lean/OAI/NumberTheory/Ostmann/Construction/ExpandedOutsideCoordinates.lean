import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduleCoordinates

namespace OAI

/-! # Every outside coordinate is an original prime coordinate -/

namespace Ostmann

open scoped Classical

def ExpandedActualCoordinates {I α : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ) (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth)) : Prop :=
  ∀ i, (∀ k, copyScheduleRole role n i.val ≠ .pivot k) →
    ∀ v ∈ current i, ∃ a : α, v = .inl a

theorem copyScheduleY_not_pivot {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (i : CopyScheduleY role n) (k : ℕ) : copyScheduleRole role n i.val ≠ .pivot k := by
  intro hk
  have hn := (surviving_pivot_is_positive role n k i.val i.property.1 hk).1
  have hc := i.property.2.1
  have he := i.property.2.2
  rw [hk] at hc he
  simp only [CopyScheduleRole.copiedAt, decide_eq_false_iff_not, CopyScheduleRole.erasedAt] at hc he
  omega

/-- Reversing a step inserts an integer only at the erased active pivot;
all other role types retain actual-prime words. -/
theorem reverseExpandedActualCoordinates {I α : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ) (b : Bool) (pivot : ExpandedScheduledVariable α depth)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable α depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current) :
    ExpandedActualCoordinates role depth n (reverseCopyLabelMap role n b [pivot] current) := by
  intro i hi v hv
  unfold reverseCopyLabelMap at hv
  split_ifs at hv with hcopy herase
  · apply hc _ _ v hv
    intro k hk
    change (copyScheduleRole role n i.val).afterCopy b = .pivot k at hk
    exact hi k ((CopyScheduleRole.afterCopy_eq_pivot _ b k).mp hk).2
  · have he := herase
    cases hr : copyScheduleRole role n i.val <;>
      simp only [hr, CopyScheduleRole.erasedAt, Bool.false_eq_true] at he
    rename_i k
    exact False.elim (hi k hr)
  · apply hc _ ?_ v hv
    intro k hk
    exact hi k hk

theorem expandedRoot_actual_coordinates {I α : Type*} (role : I → CopyScheduleRole)
    (depth : ℕ) (words : CopyScheduleAtoms role depth → List α) :
    ExpandedActualCoordinates role depth depth (fun i => (words i).map Sum.inl) := by
  intro i _ v hv
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
  exact ⟨a, rfl⟩

/-- Thus every constituent of Y is an actual prime variable even after
ancestor pivots have already been reconstructed. -/
theorem expandedYWord_actual {I α : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable α depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current)
    (i : CopyScheduleY role n) :
    ∀ v ∈ current ⟨.inr i.val, i.property⟩, ∃ a : α, v = .inl a := by
  apply hc
  exact fun k => copyScheduleY_not_pivot role n i k

end Ostmann

end OAI
