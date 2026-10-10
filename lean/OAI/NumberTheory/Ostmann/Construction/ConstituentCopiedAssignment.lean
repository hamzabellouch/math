import OAI.NumberTheory.Ostmann.Construction.ConstituentCopyEntries
import OAI.NumberTheory.Ostmann.Construction.CopiedPriorFubini

namespace OAI

/-! # Grouping the actual copied prime assignment -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituent_inverse_atom {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) :
    copyScheduleMap Sigma.fst n
      ((survivingConstituentEquiv role size n).symm ⟨v, k⟩).val = v.val := by
  rw [← copyConstituentEquiv_atom]
  exact congrArg Sigma.fst ((copyConstituentEquiv size n).apply_symm_apply ⟨v.val, k⟩)

noncomputable def constituentH {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleH role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n :=
  let j := (survivingConstituentEquiv role size n).symm ⟨⟨v.val, v.property.1⟩, k⟩
  ⟨j.val, j.property, by
    have he := constituent_inverse_atom role size n ⟨v.val, v.property.1⟩ k
    have hr := copyScheduleRole_map Sigma.fst role n j.val
    rw [he] at hr
    exact hr ▸ v.property.2⟩

noncomputable def constituentY {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleY role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n :=
  let j := (survivingConstituentEquiv role size n).symm ⟨⟨v.val, v.property.1⟩, k⟩
  ⟨j.val, j.property, by
    have he := constituent_inverse_atom role size n ⟨v.val, v.property.1⟩ k
    have hr := copyScheduleRole_map Sigma.fst role n j.val
    rw [he] at hr
    exact hr ▸ v.property.2⟩

theorem constituentH_output {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (b : Bool) (v : CopyScheduleH role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) :
    (survivingConstituentEquiv role size (n + 1)).symm
        ⟨scheduledOutputVertex role n (.inl (b, v)), k⟩ =
      scheduledOutputVertex (fun i : Σ a, Fin (size a) => role i.1) n (.inl (b, constituentH role size n v k)) := by
  apply Subtype.ext
  rfl

theorem constituentY_output {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleY role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) :
    (survivingConstituentEquiv role size (n + 1)).symm
        ⟨scheduledOutputVertex role n (.inr v), k⟩ =
      scheduledOutputVertex (fun i : Σ a, Fin (size a) => role i.1) n (.inr (constituentY role size n v k)) := by
  apply Subtype.ext
  rfl

theorem constituent_copied_assignment_word {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) (b : Bool) (v : CopyScheduleH role n) :
    ((scheduleConstituentWord role size (n + 1)
        (scheduledOutputVertex role n (.inl (b, v)))).map
      (scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r)).prod =
      ∏ k : Fin (size (copyScheduleOrigin n v.val)),
        (if b then l else r) (constituentH role size n v k) := by
  rw [scheduleConstituentWord_prod]
  apply Finset.prod_congr rfl
  intro k _
  change Fin (size (copyScheduleOrigin n v.val)) at k
  rw [constituentH_output role size n b v k]
  cases b
  · exact scheduledCopiedAssignment_right _ _ _ _ _ _
  · exact scheduledCopiedAssignment_left _ _ _ _ _ _

theorem constituent_retained_assignment_word {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) (v : CopyScheduleY role n) :
    ((scheduleConstituentWord role size (n + 1)
        (scheduledOutputVertex role n (.inr v))).map
      (scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r)).prod =
      ∏ k : Fin (size (copyScheduleOrigin n v.val)), u (constituentY role size n v k) := by
  rw [scheduleConstituentWord_prod]
  apply Finset.prod_congr rfl
  intro k _
  change Fin (size (copyScheduleOrigin n v.val)) at k
  rw [constituentY_output role size n v k]
  exact scheduledCopiedAssignment_outside _ _ _ _ _ _

/-- Taking products of the copied prime slots is exactly the atom assignment
used by the reverse transfer system. -/
theorem constituent_copied_assignment {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    (fun v => ((scheduleConstituentWord role size (n + 1) v).map
        (scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r)).prod) =
      scheduledCopiedAssignment role n
        (fun y => ∏ k, u (constituentY role size n y k))
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun h => ∏ k, r (constituentH role size n h k)) := by
  funext v
  obtain ⟨j, rfl⟩ := (copyScheduleSurvivorEquiv role n).symm.surjective v
  rcases j with ⟨b, h⟩ | y
  · cases b
    · exact (constituent_copied_assignment_word role size n u l r false h).trans
        (scheduledCopiedAssignment_right role n
          (fun y => ∏ k, u (constituentY role size n y k))
          (fun h => ∏ k, l (constituentH role size n h k))
          (fun h => ∏ k, r (constituentH role size n h k)) h).symm
    · exact (constituent_copied_assignment_word role size n u l r true h).trans
        (scheduledCopiedAssignment_left role n
          (fun y => ∏ k, u (constituentY role size n y k))
          (fun h => ∏ k, l (constituentH role size n h k))
          (fun h => ∏ k, r (constituentH role size n h k)) h).symm
  · exact (constituent_retained_assignment_word role size n u l r y).trans
      (scheduledCopiedAssignment_outside role n
        (fun y => ∏ k, u (constituentY role size n y k))
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun h => ∏ k, r (constituentH role size n h k)) y).symm

end Ostmann

end OAI
