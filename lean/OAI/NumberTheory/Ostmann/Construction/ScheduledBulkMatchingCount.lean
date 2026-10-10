import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalPermutation
import OAI.NumberTheory.Ostmann.Construction.SeparatedMatchingCount

namespace OAI

/-! # Bad overlap matchings on the actual bulk and nonbulk prime coordinates -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledPathEnumeration (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Bool) :=
  Fintype.equivOfCardEq (by simp)

abbrev ScheduledNonbulkH {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {h : CopyScheduleH role n // copyScheduleRole role n h.val ≠ .word}

noncomputable def scheduledBulkCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) :
    (Fin (2 ^ n) × Fin m) ≃
      {h : CopyScheduleH role n // copyScheduleRole role n h.val = .word} :=
  ((scheduledPathEnumeration n).prodCongr word).trans (scheduledWordHEquiv role n)

noncomputable def scheduledSplitHCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) :
    (Fin (2 ^ n) × Fin m) ⊕ ScheduledNonbulkH role n ≃ CopyScheduleH role n :=
  ((scheduledBulkCoordinates role n m word).sumCongr (Equiv.refl _)).trans
    (Equiv.sumCompl (fun h : CopyScheduleH role n => copyScheduleRole role n h.val = .word))

noncomputable def scheduledBulkLabel {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (h : CopyScheduleH role n) : Bool :=
  decide (copyScheduleRole role n h.val = .word)

theorem scheduledBulkLabel_coordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (x : (Fin (2 ^ n) × Fin m) ⊕ ScheduledNonbulkH role n) :
    scheduledBulkLabel role n (scheduledSplitHCoordinates role n m word x) = sumSide x := by
  cases x with
  | inl b =>
    change decide (copyScheduleRole role n (scheduledBulkCoordinates role n m word b).val.val = .word) = true
    exact decide_eq_true (scheduledBulkCoordinates role n m word b).property
  | inr h =>
    change decide (copyScheduleRole role n h.val.val = .word) = false
    exact decide_eq_false h.property

noncomputable def scheduledSeparatedMatching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n)) :
    PartitionMatching (@sumSide (Fin (2 ^ n) × Fin m) (ScheduledNonbulkH role n))
      (@sumSide (Fin (2 ^ n) × Fin m) (ScheduledNonbulkH role n)) :=
  ⟨((scheduledSplitHCoordinates role n m word).trans e.val).trans
      (scheduledSplitHCoordinates role n m word).symm, by
    intro x
    have h := e.property (scheduledSplitHCoordinates role n m word x)
    change sumSide ((scheduledSplitHCoordinates role n m word).symm
      (e.val (scheduledSplitHCoordinates role n m word x))) = sumSide x
    rw [← scheduledBulkLabel_coordinates role n m word
      ((scheduledSplitHCoordinates role n m word).symm (e.val (scheduledSplitHCoordinates role n m word x))),
      Equiv.apply_symm_apply, h, scheduledBulkLabel_coordinates]
    ⟩

theorem scheduledSeparatedMatching_injective {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) :
    Function.Injective (scheduledSeparatedMatching role n m word) := by
  intro e f h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  obtain ⟨x, rfl⟩ := (scheduledSplitHCoordinates role n m word).surjective a
  have he := congrArg (fun e => scheduledSplitHCoordinates role n m word (e.val x)) h
  simpa only [scheduledSeparatedMatching, Equiv.trans_apply, Equiv.apply_symm_apply] using he

/-- This predicate uses the actual leaf coordinates of each bulk prime. -/
def BadScheduledMatching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n)) : Prop :=
  BadBulkArrangement (separatedMatchingLeft (scheduledSeparatedMatching role n m word e))

theorem bad_scheduled_matching_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (hm : 0 < m) :
    (Fintype.card {e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n) //
      BadScheduledMatching role n m word e} : ℝ) ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) * (m.factorial : ℝ) ^ (2 ^ n) *
        Real.exp ((m : ℝ) * (2 ^ n : ℕ) * (Real.log (2 ^ n : ℕ) + 1) / 4) *
          (Fintype.card (ScheduledNonbulkH role n)).factorial := by
  have hc := Fintype.card_le_of_injective
    (fun e : {e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n) //
      BadScheduledMatching role n m word e} =>
      (⟨scheduledSeparatedMatching role n m word e.val, e.property⟩ :
        {e : PartitionMatching (@sumSide (Fin (2 ^ n) × Fin m) (ScheduledNonbulkH role n))
          (@sumSide (Fin (2 ^ n) × Fin m) (ScheduledNonbulkH role n)) //
          BadBulkArrangement (separatedMatchingLeft e)}))
    (fun _ _ h => Subtype.ext (scheduledSeparatedMatching_injective role n m word (congrArg Subtype.val h)))
  exact (Nat.cast_le.mpr hc).trans
    (bad_separated_matching_bound (N := ScheduledNonbulkH role n) (Nat.one_le_pow n 2 (by decide)) hm)

noncomputable def scheduledBadMatchingSet {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) : Finset (Equiv.Perm (CopyScheduleH role n)) :=
  Finset.univ.image (fun e : {e : PartitionMatching (scheduledBulkLabel role n)
    (scheduledBulkLabel role n) // BadScheduledMatching role n m word e} => e.val.val)

theorem scheduledBadMatchingSet_card_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (hm : 0 < m) :
    ((scheduledBadMatchingSet role n m word).card : ℝ) ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) * (m.factorial : ℝ) ^ (2 ^ n) *
        Real.exp ((m : ℝ) * (2 ^ n : ℕ) * (Real.log (2 ^ n : ℕ) + 1) / 4) *
          (Fintype.card (ScheduledNonbulkH role n)).factorial := by
  apply le_trans _ (bad_scheduled_matching_bound role n m word hm)
  exact_mod_cast Finset.card_image_le

end Ostmann

end OAI
