import OAI.NumberTheory.Ostmann.Construction.ConstituentScheduleMap

namespace OAI

/-! # Every current atom retains precisely its original constituent indices -/

namespace Ostmann

/-- The copied constituent labels are the current atom labels paired with
an original index inside that atom. No new prime slots appear. -/
noncomputable def copyConstituentEquiv {I : Type*} (size : I → ℕ) : (n : ℕ) →
    CopyScheduleVertex (Σ i, Fin (size i)) n ≃
      (Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)))
  | 0 => Equiv.refl _
  | n + 1 =>
    let e := copyConstituentEquiv size n
    { toFun := fun i => match i with
        | .inl (b, i) => ⟨.inl (b, (e i).1), (e i).2⟩
        | .inr i => ⟨.inr (e i).1, (e i).2⟩
      invFun := fun i => match i with
        | ⟨.inl (b, v), k⟩ => .inl (b, e.symm ⟨v, k⟩)
        | ⟨.inr v, k⟩ => .inr (e.symm ⟨v, k⟩)
      left_inv := by
        intro i
        rcases i with ⟨b, i⟩ | i
        · change Sum.inl (b, e.symm (e i)) = _
          rw [e.symm_apply_apply]
        · change Sum.inr (e.symm (e i)) = _
          rw [e.symm_apply_apply]
      right_inv := by
        rintro ⟨v, k⟩
        rcases v with ⟨b, v⟩ | v
        · exact congrArg
            (fun a : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)) =>
              (⟨.inl (b, a.1), a.2⟩ : Σ v : CopyScheduleVertex I (n + 1),
                Fin (size (copyScheduleOrigin (n + 1) v)))) (e.apply_symm_apply ⟨v, k⟩)
        · exact congrArg
            (fun a : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)) =>
              (⟨.inr a.1, a.2⟩ : Σ v : CopyScheduleVertex I (n + 1),
                Fin (size (copyScheduleOrigin (n + 1) v)))) (e.apply_symm_apply ⟨v, k⟩) }

theorem copyConstituentEquiv_atom {I : Type*} (size : I → ℕ)
    (n : ℕ) (i : CopyScheduleVertex (Σ i, Fin (size i)) n) :
    (copyConstituentEquiv size n i).1 = copyScheduleMap Sigma.fst n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i
    · exact congrArg (fun v => Sum.inl (b, v)) (ih i)
    · exact congrArg Sum.inr (ih i)

private theorem constituentForget_injective {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    Function.Injective (fun i : Σ v : {v : CopyScheduleVertex I n // CopyScheduleSurvives role n v},
        Fin (size (copyScheduleOrigin n v.val)) =>
      (⟨i.1.val, i.2⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)))) := by
  rintro ⟨⟨a, ha⟩, i⟩ ⟨⟨b, hb⟩, j⟩ hij
  change (⟨a, i⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v))) = ⟨b, j⟩ at hij
  cases hij
  rfl

/-- Surviving constituent slots are exactly a surviving atom and one of its
original prime positions. -/
noncomputable def survivingConstituentEquiv {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    {v : CopyScheduleVertex (Σ i, Fin (size i)) n //
      CopyScheduleSurvives (role ∘ Sigma.fst) n v} ≃
    (Σ v : {v : CopyScheduleVertex I n // CopyScheduleSurvives role n v},
      Fin (size (copyScheduleOrigin n v.val))) where
  toFun i := ⟨⟨(copyConstituentEquiv size n i.val).1, by
    rw [copyConstituentEquiv_atom]
    exact (copyScheduleSurvives_map_iff Sigma.fst role n i.val).mpr i.property⟩,
    (copyConstituentEquiv size n i.val).2⟩
  invFun i := ⟨(copyConstituentEquiv size n).symm ⟨i.1.val, i.2⟩, by
    apply (copyScheduleSurvives_map_iff Sigma.fst role n _).mp
    rw [← copyConstituentEquiv_atom]
    have he := congrArg Sigma.fst ((copyConstituentEquiv size n).apply_symm_apply ⟨i.1.val, i.2⟩)
    rw [he]
    exact i.1.property⟩
  left_inv i := by
    apply Subtype.ext
    exact (copyConstituentEquiv size n).symm_apply_apply i.val
  right_inv i := by
    apply constituentForget_injective role size n
    exact (copyConstituentEquiv size n).apply_symm_apply ⟨i.1.val, i.2⟩

end Ostmann

end OAI
