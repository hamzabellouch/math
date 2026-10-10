import OAI.NumberTheory.Ostmann.Construction.ConstituentWords

namespace OAI

/-! # Grouping constituents commutes with the actual H/Y copy operation -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituent_copy_entry {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ)
    (n : ℕ) (b : Bool) (v : CopyScheduleH role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) :
    ((survivingConstituentEquiv role size (n + 1)).symm
      ⟨scheduledOutputVertex role n (.inl (b, v)), k⟩).val =
    Sum.inl (b, ((survivingConstituentEquiv role size n).symm
      ⟨⟨v.val, v.property.1⟩, k⟩).val) := rfl

theorem constituent_retained_entry {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ)
    (n : ℕ) (v : CopyScheduleY role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) :
    ((survivingConstituentEquiv role size (n + 1)).symm
      ⟨scheduledOutputVertex role n (.inr v), k⟩).val =
    Sum.inr ((survivingConstituentEquiv role size n).symm
      ⟨⟨v.val, v.property.1⟩, k⟩).val := rfl

/-- The H atom in either branch is exactly the product of that branch's
copied original prime positions. -/
theorem constituent_copy_product {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ)
    (n : ℕ) (b : Bool) (v : CopyScheduleH role n)
    (q : CopyScheduleVertex (Σ i, Fin (size i)) (n + 1) → ℕ) :
    ((scheduleConstituentWord role size (n + 1) (scheduledOutputVertex role n (.inl (b, v)))).map
        (fun i => q i.val)).prod =
    ∏ k : Fin (size (copyScheduleOrigin n v.val)),
      q (.inl (b, ((survivingConstituentEquiv role size n).symm
        ⟨⟨v.val, v.property.1⟩, k⟩).val)) := by
  rw [scheduleConstituentWord_prod]
  rfl

/-- A Y atom keeps exactly the same constituent indices. -/
theorem constituent_retained_product {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ)
    (n : ℕ) (v : CopyScheduleY role n)
    (q : CopyScheduleVertex (Σ i, Fin (size i)) (n + 1) → ℕ) :
    ((scheduleConstituentWord role size (n + 1) (scheduledOutputVertex role n (.inr v))).map
        (fun i => q i.val)).prod =
    ∏ k : Fin (size (copyScheduleOrigin n v.val)),
      q (.inr ((survivingConstituentEquiv role size n).symm
        ⟨⟨v.val, v.property.1⟩, k⟩).val) := by
  rw [scheduleConstituentWord_prod]
  rfl

end Ostmann

end OAI
