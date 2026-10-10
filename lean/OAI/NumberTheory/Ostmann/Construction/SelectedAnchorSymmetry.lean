import OAI.NumberTheory.Ostmann.Construction.SelectedAnchorMatchingCount

namespace OAI

/-! # Inversion preserves the actual anchor-code matching family -/
namespace Ostmann
open scoped Classical

theorem selectedAnchorMatchingSet_symm {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : Equiv.Perm (CopyScheduleH role n))
    (he : e ∈ selectedAnchorMatchingSet role n m bulk hbulk) :
    e.symm ∈ selectedAnchorMatchingSet role n m bulk hbulk := by
  obtain ⟨hl, hc⟩ := (mem_selectedAnchorMatchingSet role n m bulk hbulk e).mp he
  have hl' : ∀ h, selectedBulkLabel role n m bulk hbulk (e.symm h) = selectedBulkLabel role n m bulk hbulk h := by
    intro h
    simpa only [e.apply_symm_apply] using (hl (e.symm h)).symm
  apply (mem_selectedAnchorMatchingSet role n m bulk hbulk e.symm).mpr
  refine ⟨hl', ?_⟩
  let f := separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk ⟨e, hl⟩)
  let f' := separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk ⟨e.symm, hl'⟩)
  intro x
  have hinv : f (f' x) = x := by
    apply (selectedBulkCoordinates role n m bulk hbulk).injective
    apply Subtype.ext
    have h := selectedBulkMatching_slot role n m bulk hbulk ⟨e, hl⟩ (f' x)
    have h' := selectedBulkMatching_slot role n m bulk hbulk ⟨e.symm, hl'⟩ x
    change e ((selectedBulkCoordinates role n m bulk hbulk (f' x)).val) =
      (selectedBulkCoordinates role n m bulk hbulk (f (f' x))).val at h
    change e.symm ((selectedBulkCoordinates role n m bulk hbulk x).val) =
      (selectedBulkCoordinates role n m bulk hbulk (f' x)).val at h'
    rw [← h', e.apply_symm_apply] at h
    exact h.symm
  have h := hc (f' x)
  change scheduledBulkAnchorCode n (f (f' x)) = scheduledBulkAnchorCode n (f' x) at h
  rw [hinv] at h
  exact h.symm

theorem selected_nonanchor_symm {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : Equiv.Perm (CopyScheduleH role n))
    (he : e ∈ cellPreservingMatchings (selectedBulkLabel role n m bulk hbulk) \
      selectedAnchorMatchingSet role n m bulk hbulk) :
    e.symm ∈ cellPreservingMatchings (selectedBulkLabel role n m bulk hbulk) \
      selectedAnchorMatchingSet role n m bulk hbulk := by
  obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp he
  apply Finset.mem_sdiff.mpr
  constructor
  · apply (mem_cellPreservingMatchings _ _).mpr
    intro h
    have hx := ((mem_cellPreservingMatchings _ _).mp hl) (e.symm h)
    simpa only [e.apply_symm_apply] using hx.symm
  · intro h
    exact hn (by simpa only [Equiv.symm_symm] using selectedAnchorMatchingSet_symm role n m bulk hbulk e.symm h)

end Ostmann

end OAI
