import OAI.NumberTheory.Ostmann.Construction.SelectedBulkCoordinates
import OAI.NumberTheory.Ostmann.Construction.ScheduledAnchorMatchingCount

namespace OAI

/-! # Code-preserving matchings of the selected bulk, excluding the top slot -/
namespace Ostmann
open scoped Classical

def PreservesSelectedAnchorCode {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : PartitionMatching (selectedBulkLabel role n m bulk hbulk) (selectedBulkLabel role n m bulk hbulk)) : Prop :=
  ∀ x, scheduledBulkAnchorCode n
    (separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e) x) =
      scheduledBulkAnchorCode n x

theorem selected_anchor_matching_count {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    Fintype.card {e : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
      (selectedBulkLabel role n m bulk hbulk) // PreservesSelectedAnchorCode role n m bulk hbulk e} ≤
      (2 * m) ^ (2 ^ n * m) * (Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial := by
  let f : {e : PartitionMatching (selectedBulkLabel role n m bulk hbulk) (selectedBulkLabel role n m bulk hbulk) //
      PreservesSelectedAnchorCode role n m bulk hbulk e} →
      PartitionMatching (@scheduledBulkAnchorCode n m) (@scheduledBulkAnchorCode n m) ×
        Equiv.Perm (SelectedNonbulkH role n m bulk hbulk) :=
    fun e => (⟨separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e.val), e.property⟩,
      separatedMatchingRight (selectedSeparatedMatching role n m bulk hbulk e.val))
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    apply selectedSeparatedMatching_injective role n m bulk hbulk
    apply separatedMatching_pair_injective
    have hl : separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e.val) =
        separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e'.val) :=
      congrArg (fun z => z.1.val) h
    have hr : separatedMatchingRight (selectedSeparatedMatching role n m bulk hbulk e.val) =
        separatedMatchingRight (selectedSeparatedMatching role n m bulk hbulk e'.val) :=
      congrArg Prod.snd h
    exact Prod.ext hl hr
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_perm] at hc
  exact hc.trans (Nat.mul_le_mul_right _ (card_scheduled_bulk_anchor_matching n m))

noncomputable def selectedAnchorMatchingSet {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) : Finset (Equiv.Perm (CopyScheduleH role n)) :=
  Finset.univ.image (fun e : {e : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
    (selectedBulkLabel role n m bulk hbulk) // PreservesSelectedAnchorCode role n m bulk hbulk e} => e.val.val)

theorem selectedAnchorMatchingSet_card_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (selectedAnchorMatchingSet role n m bulk hbulk).card ≤
      (2 * m) ^ (2 ^ n * m) * (Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial :=
  (Finset.card_image_le.trans_eq (by simp)).trans (selected_anchor_matching_count role n m bulk hbulk)

@[simp] theorem mem_selectedAnchorMatchingSet {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e : Equiv.Perm (CopyScheduleH role n)) :
    e ∈ selectedAnchorMatchingSet role n m bulk hbulk ↔
      ∃ h : ∀ x, selectedBulkLabel role n m bulk hbulk (e x) = selectedBulkLabel role n m bulk hbulk x,
        PreservesSelectedAnchorCode role n m bulk hbulk ⟨e, h⟩ := by
  simp only [selectedAnchorMatchingSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨⟨f, hf⟩, hc⟩, rfl⟩
    exact ⟨hf, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨⟨e, h⟩, hc⟩, rfl⟩

theorem selectedAnchorMatchingSet_subset {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    selectedAnchorMatchingSet role n m bulk hbulk ⊆ cellPreservingMatchings (selectedBulkLabel role n m bulk hbulk) := by
  intro e he
  obtain ⟨h, _⟩ := (mem_selectedAnchorMatchingSet role n m bulk hbulk e).mp he
  exact (mem_cellPreservingMatchings _ _).mpr h

end Ostmann

end OAI
