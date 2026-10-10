import OAI.NumberTheory.Ostmann.Construction.SchedulePivotSlots
import OAI.NumberTheory.Ostmann.Construction.ScheduledTransferGraph

namespace OAI

/-! # The exact current pivot/H/Y partition of surviving prime slots -/

namespace Ostmann

open scoped Classical

abbrev CurrentPivotConstituent {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {i : I // role i = .pivot n}

noncomputable def scheduledPartitionMap {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    CurrentPivotConstituent role n ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n) →
      {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i}
  | .inl p => ⟨copySchedulePositive n p.val,
      copyScheduleSurvives_positive role p.val n p.property n le_rfl⟩
  | .inr (.inl h) => ⟨h.val, h.property.1⟩
  | .inr (.inr y) => ⟨y.val, y.property.1⟩

private theorem scheduledPartitionMap_injective {I : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) :
    Function.Injective (scheduledPartitionMap role n) := by
  intro a b he
  have hv := congrArg Subtype.val he
  rcases a with p | h | y <;> rcases b with q | h' | y' <;>
    dsimp only [scheduledPartitionMap] at hv
  · exact congrArg Sum.inl (Subtype.ext (copySchedulePositive_injective n hv))
  · have hc := h'.property.2
    rw [← hv, copyScheduleRole_positive role p.val n p.property] at hc
    simp [CopyScheduleRole.copiedAt] at hc
  · have hc := y'.property.2.2
    rw [← hv, copyScheduleRole_positive role p.val n p.property] at hc
    simp [CopyScheduleRole.erasedAt] at hc
  · have hc := h.property.2
    rw [hv, copyScheduleRole_positive role q.val n q.property] at hc
    simp [CopyScheduleRole.copiedAt] at hc
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext hv)
  · have hc := h.property.2
    rw [hv, y'.property.2.1] at hc
    cases hc
  · have hc := y.property.2.2
    rw [hv, copyScheduleRole_positive role q.val n q.property] at hc
    simp [CopyScheduleRole.erasedAt] at hc
  · have hc := h'.property.2
    rw [← hv, y.property.2.1] at hc
    cases hc
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext hv)

private theorem scheduledPartitionMap_surjective {I : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) :
    Function.Surjective (scheduledPartitionMap role n) := by
  intro v
  by_cases hc : (copyScheduleRole role n v.val).copiedAt n = true
  · exact ⟨.inr (.inl ⟨v.val, v.property, hc⟩), rfl⟩
  have hc' : (copyScheduleRole role n v.val).copiedAt n = false := by
    cases hh : (copyScheduleRole role n v.val).copiedAt n <;> simp_all
  by_cases he : (copyScheduleRole role n v.val).erasedAt n = true
  · have hp : copyScheduleRole role n v.val = .pivot n := by
      cases hr : copyScheduleRole role n v.val with
      | pivot k =>
        have : n = k := by simpa [CopyScheduleRole.erasedAt, hr] using he
        subst k
        rfl
      | word => simp [CopyScheduleRole.erasedAt, hr] at he
      | anchor k => simp [CopyScheduleRole.erasedAt, hr] at he
      | outside => simp [CopyScheduleRole.erasedAt, hr] at he
    obtain ⟨_, p, hp, hv⟩ := surviving_pivot_is_positive role n n v.val v.property hp
    exact ⟨.inl ⟨p, hp⟩, Subtype.ext hv.symm⟩
  · have he' : (copyScheduleRole role n v.val).erasedAt n = false := by
      cases hh : (copyScheduleRole role n v.val).erasedAt n <;> simp_all
    exact ⟨.inr (.inr ⟨v.val, v.property, hc', he'⟩), rfl⟩

noncomputable def scheduledPartitionEquiv {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    CurrentPivotConstituent role n ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n) ≃
      {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} :=
  Equiv.ofBijective (scheduledPartitionMap role n)
    ⟨scheduledPartitionMap_injective role n, scheduledPartitionMap_surjective role n⟩

@[simp] theorem scheduledPartitionEquiv_pivot {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (p : CurrentPivotConstituent role n) :
    (scheduledPartitionEquiv role n (.inl p)).val = copySchedulePositive n p.val := rfl

@[simp] theorem scheduledPartitionEquiv_rest {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (i : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    (scheduledPartitionEquiv role n (.inr i)).val = Sum.elim Subtype.val Subtype.val i := by
  cases i <;> rfl

end Ostmann

end OAI
