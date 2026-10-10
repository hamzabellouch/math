import OAI.NumberTheory.Ostmann.Construction.ScheduledWordLeafProducts

namespace OAI

/-! # Reversal keeps unexposed leaf primes out of every outside coordinate -/

namespace Ostmann
open scoped Classical

theorem reverseCopyLabelMap_wordOutside_independent {I A : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ) (b : Bool) (P : A)
    (y : WordLeafOutside role i hi (n + 1) → A)
    (x x' : TreeLeafIndex (n + 1) → A) (v : WordLeafOutside role i hi n) :
    reverseCopyLabelMap role n b P (wordLeafAssignment role i hi (n + 1) y x) v.val =
      reverseCopyLabelMap role n b P (wordLeafAssignment role i hi (n + 1) y x') v.val := by
  by_cases hc : (copyScheduleRole role n v.val.val).copiedAt n = true
  · let h : CopyScheduleH role n := ⟨v.val.val, v.val.property, hc⟩
    have hh : h ∉ Set.range (wordLeafHSlot role i hi n) := by
      rintro ⟨t, ht⟩
      apply v.property
      exact ⟨t, Subtype.ext (congrArg (fun h : CopyScheduleH role n => h.val) ht)⟩
    let z := copiedWordLeafOutside role i hi n b ⟨h, hh⟩
    rw [reverseCopyLabelMap, dite_eq_left hc, reverseCopyLabelMap, dite_eq_left hc]
    exact (wordLeafAssignment_outside role i hi (n + 1) y x z).trans
      (wordLeafAssignment_outside role i hi (n + 1) y x' z).symm
  · by_cases he : (copyScheduleRole role n v.val.val).erasedAt n = true
    · rw [reverseCopyLabelMap, dite_eq_right hc, dite_eq_left he,
        reverseCopyLabelMap, dite_eq_right hc, dite_eq_left he]
    · let z : WordLeafOutside role i hi (n + 1) :=
        ⟨⟨.inr v.val.val, v.val.property, Bool.eq_false_iff.mpr hc, Bool.eq_false_iff.mpr he⟩, by
          rintro ⟨t, ht⟩
          have hv := congrArg (fun a : CopyScheduleAtoms role (n + 1) => a.val) ht
          cases t with
          | inl t => rw [wordLeafSlot_left] at hv; cases hv
          | inr t => rw [wordLeafSlot_right] at hv; cases hv⟩
      rw [reverseCopyLabelMap, dite_eq_right hc, dite_eq_right he,
        reverseCopyLabelMap, dite_eq_right hc, dite_eq_right he]
      exact (wordLeafAssignment_outside role i hi (n + 1) y x z).trans
        (wordLeafAssignment_outside role i hi (n + 1) y x' z).symm

noncomputable def reversedWordOutside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (b : Bool) (P : ℕ)
    (y : WordLeafOutside role i hi (n + 1) → ℕ) : WordLeafOutside role i hi n → ℕ :=
  fun v => reverseCopyLabelMap role n b P
    (wordLeafAssignment role i hi (n + 1) y (fun _ => 1)) v.val

/-- Each child has precisely its own unexposed leaf primes. All other child
coordinates are functions of the old outside assignment and the forced pivot. -/
theorem reverseCopyLabelMap_wordLeaf_assignment {I : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ) (b : Bool) (P : ℕ)
    (y : WordLeafOutside role i hi (n + 1) → ℕ) (x : TreeLeafIndex (n + 1) → ℕ) :
    reverseCopyLabelMap role n b P (wordLeafAssignment role i hi (n + 1) y x) =
      wordLeafAssignment role i hi n (reversedWordOutside role i hi n b P y)
        (fun t => x (if b then .inl t else .inr t)) := by
  funext v
  obtain ⟨z, rfl⟩ := (wordLeafPartition role i hi n).surjective v
  cases z with
  | inl t =>
    rw [wordLeafPartition_leaf, reverseCopyLabelMap_wordLeaf,
      wordLeafAssignment_leaf, wordLeafAssignment_leaf]
  | inr v =>
    rw [wordLeafPartition_outside, wordLeafAssignment_outside]
    exact reverseCopyLabelMap_wordOutside_independent role i hi n b P y x (fun _ => 1) v

end Ostmann

end OAI
