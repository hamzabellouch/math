import OAI.NumberTheory.Ostmann.Construction.ActiveNonbulkCount
import OAI.NumberTheory.Ostmann.Construction.ScheduledTreeBulkCoordinates

namespace OAI

/-! # Bulk coordinates inside a larger word

The selected bulk slots are copied with the whole word. The top slot is
retained in that word but belongs to the complementary matching block.
-/
namespace Ostmann
open scoped Classical

noncomputable def selectedBulkH {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (Fin (2 ^ n) × Fin m) ↪ CopyScheduleH role n where
  toFun x := scheduledWordH role n (scheduledPathEnumeration n x.1) ⟨bulk x.2, hbulk x.2⟩
  inj' := by
    intro x y h
    have he := @copySchedulePath_injective I n
      (scheduledPathEnumeration n x.1, bulk x.2) (scheduledPathEnumeration n y.1, bulk y.2)
      (congrArg Subtype.val h)
    exact Prod.ext ((scheduledPathEnumeration n).injective (congrArg Prod.fst he))
      (bulk.injective (congrArg Prod.snd he))

abbrev SelectedNonbulkH {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :=
  {h : CopyScheduleH role n // h ∉ Set.range (selectedBulkH role n m bulk hbulk)}

noncomputable def selectedBulkCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (Fin (2 ^ n) × Fin m) ≃
      {h : CopyScheduleH role n // h ∈ Set.range (selectedBulkH role n m bulk hbulk)} :=
  Equiv.ofInjective _ (selectedBulkH role n m bulk hbulk).injective

noncomputable def selectedSplitHCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (Fin (2 ^ n) × Fin m) ⊕ SelectedNonbulkH role n m bulk hbulk ≃ CopyScheduleH role n :=
  ((selectedBulkCoordinates role n m bulk hbulk).sumCongr (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range (selectedBulkH role n m bulk hbulk)))

noncomputable def selectedBulkLabel {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (h : CopyScheduleH role n) : Bool :=
  decide (h ∈ Set.range (selectedBulkH role n m bulk hbulk))

theorem selectedBulkLabel_coordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (x : (Fin (2 ^ n) × Fin m) ⊕ SelectedNonbulkH role n m bulk hbulk) :
    selectedBulkLabel role n m bulk hbulk (selectedSplitHCoordinates role n m bulk hbulk x) =
      sumSide x := by
  cases x with
  | inl b =>
    change decide ((selectedBulkCoordinates role n m bulk hbulk b).val ∈
      Set.range (selectedBulkH role n m bulk hbulk)) = true
    exact decide_eq_true (selectedBulkCoordinates role n m bulk hbulk b).property
  | inr h =>
    change decide (h.val ∈ Set.range (selectedBulkH role n m bulk hbulk)) = false
    exact decide_eq_false h.property

noncomputable def selectedSeparatedMatching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
      (selectedBulkLabel role n m bulk hbulk)) :
    PartitionMatching (@sumSide (Fin (2 ^ n) × Fin m) (SelectedNonbulkH role n m bulk hbulk))
      (@sumSide (Fin (2 ^ n) × Fin m) (SelectedNonbulkH role n m bulk hbulk)) :=
  ⟨((selectedSplitHCoordinates role n m bulk hbulk).trans e.val).trans
      (selectedSplitHCoordinates role n m bulk hbulk).symm, by
    intro x
    have h := e.property (selectedSplitHCoordinates role n m bulk hbulk x)
    change sumSide ((selectedSplitHCoordinates role n m bulk hbulk).symm
      (e.val (selectedSplitHCoordinates role n m bulk hbulk x))) = sumSide x
    rw [← selectedBulkLabel_coordinates role n m bulk hbulk
      ((selectedSplitHCoordinates role n m bulk hbulk).symm
        (e.val (selectedSplitHCoordinates role n m bulk hbulk x))),
      Equiv.apply_symm_apply, h, selectedBulkLabel_coordinates]⟩

theorem selectedSeparatedMatching_injective {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    Function.Injective (selectedSeparatedMatching role n m bulk hbulk) := by
  intro e f h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  obtain ⟨x, rfl⟩ := (selectedSplitHCoordinates role n m bulk hbulk).surjective a
  have he := congrArg (fun e => selectedSplitHCoordinates role n m bulk hbulk (e.val x)) h
  simpa only [selectedSeparatedMatching, Equiv.trans_apply, Equiv.apply_symm_apply] using he

@[simp] theorem selectedSplitHCoordinates_inl {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (x : Fin (2 ^ n) × Fin m) :
    selectedSplitHCoordinates role n m bulk hbulk (.inl x) = selectedBulkH role n m bulk hbulk x := rfl

theorem selectedBulkMatching_slot {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
      (selectedBulkLabel role n m bulk hbulk)) (x : Fin (2 ^ n) × Fin m) :
    e.val (selectedBulkH role n m bulk hbulk x) =
      selectedBulkH role n m bulk hbulk
        (separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e) x) := by
  have h := congrArg (selectedSplitHCoordinates role n m bulk hbulk)
    (separatedMatchingLeft_apply (selectedSeparatedMatching role n m bulk hbulk e) x)
  simpa only [selectedSeparatedMatching, Equiv.trans_apply, Equiv.apply_symm_apply,
    selectedSplitHCoordinates_inl] using h

/-- An H slot over an original bulk position is one of the selected leaves. -/
theorem mem_selectedBulkH_of_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (h : CopyScheduleH role n) (i : Fin m) (hi : copyScheduleOrigin n h.val = bulk i) :
    h ∈ Set.range (selectedBulkH role n m bulk hbulk) := by
  have hw : copyScheduleRole role n h.val = .word :=
    copyScheduleRole_origin_word role n h.val (hi ▸ hbulk i)
  obtain ⟨t, j, hj, he⟩ := surviving_word_is_path role n h.val h.property.1 hw
  have hji : j = bulk i := by
    have hh := congrArg (copyScheduleOrigin n) he
    simpa only [copyScheduleOrigin_path, hi] using hh.symm
  subst j
  refine ⟨((scheduledPathEnumeration n).symm t, i), ?_⟩
  apply Subtype.ext
  change copySchedulePath n (scheduledPathEnumeration n ((scheduledPathEnumeration n).symm t))
    (bulk i) = h.val
  simpa only [Equiv.apply_symm_apply] using he.symm

theorem selectedNonbulkH_card_active {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ) (bulk : Fin m ↪ I)
    (hbulk : ∀ i, role (bulk i) = .word) :
    Fintype.card (SelectedNonbulkH role n m bulk hbulk) ≤
      2 ^ n * Fintype.card {i : I // i ∉ Set.range bulk ∧ role i ≠ .outside} := by
  let code : SelectedNonbulkH role n m bulk hbulk →
      (Fin n → Bool) × {i : I // i ∉ Set.range bulk ∧ role i ≠ .outside} :=
    fun h => (survivorTrace n h.val.val, ⟨copyScheduleOrigin n h.val.val, by
      constructor
      · rintro ⟨i, hi⟩
        exact h.property (mem_selectedBulkH_of_origin role n m bulk hbulk h.val i hi.symm)
      · exact copyScheduleH_origin_not_outside role n h.val⟩)
  have hc : Function.Injective code := by
    intro i j h
    apply Subtype.ext
    apply Subtype.ext
    exact survivorTrace_origin_injective role n i.val.val j.val.val i.val.property.1
      j.val.property.1 (congrArg Prod.fst h) (congrArg (fun z => z.2.val) h)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    using Fintype.card_le_of_injective code hc

end Ostmann

end OAI
