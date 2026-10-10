import OAI.NumberTheory.Ostmann.Construction.ScheduledWordLeafPrior

namespace OAI

/-! # The selected prime products in the two actual H branches -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def wordLeafHSlot {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) : TreeLeafIndex n ↪ CopyScheduleH role n where
  toFun t := ⟨(wordLeafSlot role i hi n t).val, (wordLeafSlot role i hi n t).property, by
    rw [wordLeafSlot_role]
    rfl⟩
  inj' := by
    intro a b h
    apply (wordLeafSlot role i hi n).injective
    have hv : (wordLeafSlot role i hi n a).val = (wordLeafSlot role i hi n b).val :=
      congrArg (fun z : CopyScheduleH role n => z.val) h
    exact Subtype.ext hv

abbrev WordLeafHOutside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :=
  {h : CopyScheduleH role n // h ∉ Set.range (wordLeafHSlot role i hi n)}

noncomputable def wordLeafHPartition {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :
    TreeLeafIndex n ⊕ WordLeafHOutside role i hi n ≃ CopyScheduleH role n :=
  (Equiv.sumCongr (Equiv.ofInjective _ (wordLeafHSlot role i hi n).injective)
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (wordLeafHSlot role i hi n)))

theorem copied_wordLeafHSlot {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (b : Bool) (t : TreeLeafIndex n) :
    (⟨.inl (b, (wordLeafHSlot role i hi n t).val),
      (wordLeafHSlot role i hi n t).property⟩ : CopyScheduleAtoms role (n + 1)) =
      wordLeafSlot role i hi (n + 1) (if b then .inl t else .inr t) := by
  apply Subtype.ext
  cases b
  · exact (wordLeafSlot_right role i hi n t).symm
  · exact (wordLeafSlot_left role i hi n t).symm

/-- Every other H coordinate is among the primes held fixed in the
conditional leaf expectation, including the currently sampled pivot groups. -/
noncomputable def copiedWordLeafOutside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (b : Bool)
    (h : WordLeafHOutside role i hi n) : WordLeafOutside role i hi (n + 1) :=
  ⟨⟨.inl (b, h.val.val), h.val.property⟩, by
    rintro ⟨t, ht⟩
    apply h.property
    cases t with
    | inl t =>
      have he : Sum.inl (true, (wordLeafSlot role i hi n t).val) =
          (Sum.inl (b, h.val.val) : CopyScheduleVertex I (n + 1)) :=
        (wordLeafSlot_left role i hi n t).symm.trans (congrArg Subtype.val ht)
      exact ⟨t, Subtype.ext (congrArg Prod.snd (Sum.inl.inj he))⟩
    | inr t =>
      have he : Sum.inl (false, (wordLeafSlot role i hi n t).val) =
          (Sum.inl (b, h.val.val) : CopyScheduleVertex I (n + 1)) :=
        (wordLeafSlot_right role i hi n t).symm.trans (congrArg Subtype.val ht)
      exact ⟨t, Subtype.ext (congrArg Prod.snd (Sum.inl.inj he))⟩⟩

/-- The actual H product factors into a fixed coefficient and the selected
leaf-prime product. This is an equality before any coprimality restriction. -/
theorem wordLeaf_H_product {I M : Type*} [Fintype I] [CommMonoid M]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ) (b : Bool)
    (y : WordLeafOutside role i hi (n + 1) → M) (x : TreeLeafIndex (n + 1) → M) :
    (∏ h : CopyScheduleH role n,
      wordLeafAssignment role i hi (n + 1) y x ⟨.inl (b, h.val), h.property⟩) =
      (∏ h : WordLeafHOutside role i hi n, y (copiedWordLeafOutside role i hi n b h)) *
        ∏ t : TreeLeafIndex n, x (if b then .inl t else .inr t) := by
  rw [← (wordLeafHPartition role i hi n).prod_comp]
  rw [Fintype.prod_sum_type]
  have hleft :
      (∏ t : TreeLeafIndex n, wordLeafAssignment role i hi (n + 1) y x
        ⟨.inl (b, (wordLeafHPartition role i hi n (.inl t)).val),
          (wordLeafHPartition role i hi n (.inl t)).property⟩) =
        ∏ t : TreeLeafIndex n, x (if b then .inl t else .inr t) := by
    apply Finset.prod_congr rfl
    intro t _
    change wordLeafAssignment role i hi (n + 1) y x
      ⟨.inl (b, (wordLeafHSlot role i hi n t).val),
        (wordLeafHSlot role i hi n t).property⟩ = _
    rw [copied_wordLeafHSlot, wordLeafAssignment_leaf]
  have hright :
      (∏ h : WordLeafHOutside role i hi n, wordLeafAssignment role i hi (n + 1) y x
        ⟨.inl (b, (wordLeafHPartition role i hi n (.inr h)).val),
          (wordLeafHPartition role i hi n (.inr h)).property⟩) =
        ∏ h : WordLeafHOutside role i hi n, y (copiedWordLeafOutside role i hi n b h) := by
    apply Finset.prod_congr rfl
    intro h _
    exact wordLeafAssignment_outside role i hi (n + 1) y x
      (copiedWordLeafOutside role i hi n b h)
  rw [hleft, hright, mul_comm]

end Ostmann

end OAI
