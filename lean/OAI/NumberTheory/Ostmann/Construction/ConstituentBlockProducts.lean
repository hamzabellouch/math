import OAI.NumberTheory.Ostmann.Construction.ConstituentCopiedAssignment

namespace OAI

/-! # Exact products of all constituents in an H or Y block -/

namespace Ostmann

open scoped BigOperators Classical

private theorem blockForget_injective {I : Type*} (size : I → ℕ) (n : ℕ)
    (P : CopyScheduleVertex I n → Prop) :
    Function.Injective (fun z : Σ v : {v // P v}, Fin (size (copyScheduleOrigin n v.val)) =>
      (⟨z.1.val, z.2⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)))) := by
  rintro ⟨⟨a, ha⟩, i⟩ ⟨⟨b, hb⟩, j⟩ he
  change (⟨a, i⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v))) = ⟨b, j⟩ at he
  cases he
  rfl

noncomputable def constituentHEquiv {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    (Σ v : CopyScheduleH role n, Fin (size (copyScheduleOrigin n v.val))) ≃
      CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n :=
  Equiv.ofBijective (fun z => constituentH role size n z.1 z.2) (by
    constructor
    · intro a b he
      apply blockForget_injective size n
      have hs : (survivingConstituentEquiv role size n).symm ⟨⟨a.1.val, a.1.property.1⟩, a.2⟩ =
          (survivingConstituentEquiv role size n).symm ⟨⟨b.1.val, b.1.property.1⟩, b.2⟩ :=
        Subtype.ext (congrArg (fun q : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n => q.val) he)
      exact congrArg (fun z : Σ v : CopyScheduleAtoms role n, Fin (size (copyScheduleOrigin n v.val)) =>
        (⟨z.1.val, z.2⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v))))
        ((survivingConstituentEquiv role size n).symm.injective hs)
    · intro q
      let z := survivingConstituentEquiv role size n ⟨q.val, q.property.1⟩
      have hr : copyScheduleRole role n z.1.val =
          copyScheduleRole (fun i : Σ a, Fin (size a) => role i.1) n q.val := by
        change copyScheduleRole role n (copyConstituentEquiv size n q.val).1 = _
        rw [copyConstituentEquiv_atom]
        exact copyScheduleRole_map Sigma.fst role n q.val
      let v : CopyScheduleH role n := ⟨z.1.val, z.1.property, hr.symm ▸ q.property.2⟩
      refine ⟨⟨v, z.2⟩, ?_⟩
      apply Subtype.ext
      exact congrArg (fun q : SurvivingConstituent role size n => q.val)
        ((survivingConstituentEquiv role size n).symm_apply_apply
        ⟨q.val, q.property.1⟩))

noncomputable def constituentYEquiv {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    (Σ v : CopyScheduleY role n, Fin (size (copyScheduleOrigin n v.val))) ≃
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n :=
  Equiv.ofBijective (fun z => constituentY role size n z.1 z.2) (by
    constructor
    · intro a b he
      apply blockForget_injective size n
      have hs : (survivingConstituentEquiv role size n).symm ⟨⟨a.1.val, a.1.property.1⟩, a.2⟩ =
          (survivingConstituentEquiv role size n).symm ⟨⟨b.1.val, b.1.property.1⟩, b.2⟩ :=
        Subtype.ext (congrArg (fun q : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n => q.val) he)
      exact congrArg (fun z : Σ v : CopyScheduleAtoms role n, Fin (size (copyScheduleOrigin n v.val)) =>
        (⟨z.1.val, z.2⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v))))
        ((survivingConstituentEquiv role size n).symm.injective hs)
    · intro q
      let z := survivingConstituentEquiv role size n ⟨q.val, q.property.1⟩
      have hr : copyScheduleRole role n z.1.val =
          copyScheduleRole (fun i : Σ a, Fin (size a) => role i.1) n q.val := by
        change copyScheduleRole role n (copyConstituentEquiv size n q.val).1 = _
        rw [copyConstituentEquiv_atom]
        exact copyScheduleRole_map Sigma.fst role n q.val
      let v : CopyScheduleY role n := ⟨z.1.val, z.1.property, hr.symm ▸ q.property.2⟩
      refine ⟨⟨v, z.2⟩, ?_⟩
      apply Subtype.ext
      exact congrArg (fun q : SurvivingConstituent role size n => q.val)
        ((survivingConstituentEquiv role size n).symm_apply_apply
        ⟨q.val, q.property.1⟩))

theorem constituentH_product {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    (∏ h : CopyScheduleH role n, ∏ k, l (constituentH role size n h k)) = ∏ h, l h := by
  rw [← Fintype.prod_sigma (fun z : Σ h : CopyScheduleH role n, Fin (size (copyScheduleOrigin n h.val)) =>
    l (constituentH role size n z.1 z.2))]
  exact (constituentHEquiv role size n).prod_comp l

theorem constituentY_product {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    (∏ y : CopyScheduleY role n, ∏ k, u (constituentY role size n y k)) = ∏ y, u y := by
  rw [← Fintype.prod_sigma (fun z : Σ y : CopyScheduleY role n, Fin (size (copyScheduleOrigin n y.val)) =>
    u (constituentY role size n z.1 z.2))]
  exact (constituentYEquiv role size n).prod_comp u

end Ostmann

end OAI
