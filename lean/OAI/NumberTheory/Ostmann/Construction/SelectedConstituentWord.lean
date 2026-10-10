import OAI.NumberTheory.Ostmann.Construction.SelectedWordReversal
import OAI.NumberTheory.Ostmann.Construction.ConstituentCopiedAssignment

namespace OAI

/-! # One selected prime per composite word, under the original grouping -/

namespace Ostmann
open scoped BigOperators Classical

theorem wordLeafSlot_atom {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ) (t : TreeLeafIndex n) :
    (survivingConstituentEquiv role size n
      (wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n t)).1 =
      wordLeafSlot role i.1 hi n t := by
  apply Subtype.ext
  change (copyConstituentEquiv size n (copySchedulePath n (treeLeafCopyPath n t) i)).1 = _
  rw [copyConstituentEquiv_atom, copyScheduleMap_path]
  rfl

theorem wordLeafSlot_constituent_exists {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (i : Σ a, Fin (size a)) (hi : role i.1 = .word)
    (n : ℕ) (t : TreeLeafIndex n) :
    ∃ k : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val)),
      (survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, k⟩ =
        wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n t := by
  obtain ⟨⟨a, k⟩, hk⟩ := (survivingConstituentEquiv role size n).symm.surjective
    (wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n t)
  have ha := wordLeafSlot_atom role size i hi n t
  rw [← hk, Equiv.apply_symm_apply] at ha
  dsimp only at ha
  subst a
  exact ⟨k, hk⟩

theorem constituent_outside_selected_word {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (a : WordLeafOutside role i.1 hi n)
    (k : Fin (size (copyScheduleOrigin n a.val.val))) :
    (survivingConstituentEquiv role size n).symm ⟨a.val, k⟩ ∉
      Set.range (wordLeafSlot (fun j : Σ b, Fin (size b) => role j.1) i hi n) := by
  rintro ⟨t, ht⟩
  apply a.property
  refine ⟨t, ?_⟩
  have ha := wordLeafSlot_atom role size i hi n t
  rw [ht, Equiv.apply_symm_apply] at ha
  exact ha.symm

theorem other_constituent_outside_selected_primes {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ) (t : TreeLeafIndex n)
    (k : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val)))
    (hk : (survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, k⟩ =
      wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n t)
    (j : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val))) (hjk : j ≠ k) :
    (survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, j⟩ ∉
      Set.range (wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n) := by
  rintro ⟨u, hu⟩
  have ha := wordLeafSlot_atom role size i hi n u
  rw [hu, Equiv.apply_symm_apply] at ha
  have hut : u = t := (wordLeafSlot role i.1 hi n).injective ha.symm
  subst u
  have he := (survivingConstituentEquiv role size n).symm.injective (hu.symm.trans hk.symm)
  exact hjk (eq_of_heq (Sigma.mk.inj_iff.mp he).2)

section
variable {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ)
variable (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
variable (y : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n → ℕ)
variable (x : TreeLeafIndex n → ℕ)

theorem grouped_wordLeaf_outside (a : WordLeafOutside role i.1 hi n) :
    ((scheduleConstituentWord role size n a.val).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x)).prod =
    ((scheduleConstituentWord role size n a.val).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod := by
  rw [scheduleConstituentWord_prod, scheduleConstituentWord_prod]
  apply Finset.prod_congr rfl
  intro k _
  let z := (survivingConstituentEquiv role size n).symm ⟨a.val, k⟩
  let o : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n :=
    ⟨z, constituent_outside_selected_word role size i hi n a k⟩
  exact (wordLeafAssignment_outside _ i hi n y x o).trans
    (wordLeafAssignment_outside _ i hi n y (fun _ => 1) o).symm

theorem grouped_wordLeaf_selected (t : TreeLeafIndex n) :
    ((scheduleConstituentWord role size n (wordLeafSlot role i.1 hi n t)).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x)).prod =
    ((scheduleConstituentWord role size n (wordLeafSlot role i.1 hi n t)).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod * x t := by
  obtain ⟨k, hk⟩ := wordLeafSlot_constituent_exists role size i hi n t
  rw [scheduleConstituentWord_prod, scheduleConstituentWord_prod]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k, Fintype.prod_eq_mul_prod_subtype_ne _ k]
  rw [hk, wordLeafAssignment_leaf, wordLeafAssignment_leaf, one_mul]
  have he :
      (∏ j : {j : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val)) // j ≠ k},
        wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x
          ((survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, j.val⟩)) =
      ∏ j : {j : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val)) // j ≠ k},
        wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1)
          ((survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, j.val⟩) := by
    apply Finset.prod_congr rfl
    intro j _
    let o : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n :=
      ⟨_, other_constituent_outside_selected_primes role size i hi n t k hk j.val j.property⟩
    exact (wordLeafAssignment_outside _ i hi n y x o).trans
      (wordLeafAssignment_outside _ i hi n y (fun _ => 1) o).symm
  rw [he, mul_comm]

/-- Grouping introduces a fixed multiplier in each selected word, while
every other atom is independent of the unexposed selected primes. -/
theorem grouped_wordLeaf_assignment :
    (fun a : CopyScheduleAtoms role n => ((scheduleConstituentWord role size n a).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x)).prod) =
    wordLeafAssignment role i.1 hi n
      (fun a => ((scheduleConstituentWord role size n a.val).map
        (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod)
      (fun t => ((scheduleConstituentWord role size n (wordLeafSlot role i.1 hi n t)).map
        (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod * x t) := by
  funext a
  obtain ⟨z, rfl⟩ := (wordLeafPartition role i.1 hi n).surjective a
  cases z with
  | inl t =>
    rw [wordLeafPartition_leaf, wordLeafAssignment_leaf]
    exact grouped_wordLeaf_selected role size i hi n y x t
  | inr a =>
    rw [wordLeafPartition_outside, wordLeafAssignment_outside]
    exact grouped_wordLeaf_outside role size i hi n y x a

end
end Ostmann

end OAI
