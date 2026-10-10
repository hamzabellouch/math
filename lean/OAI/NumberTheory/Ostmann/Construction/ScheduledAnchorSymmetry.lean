import OAI.NumberTheory.Ostmann.Construction.ScheduledAnchorMatchingCount

namespace OAI

/-! # Inversion preserves the actual anchor-code matching family -/
namespace Ostmann
open scoped Classical

theorem scheduledAnchorMatchingSet_symm {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (e : Equiv.Perm (CopyScheduleH role n))
    (he : e ∈ scheduledAnchorMatchingSet role n m word) :
    e.symm ∈ scheduledAnchorMatchingSet role n m word := by
  obtain ⟨hl, hc⟩ := (mem_scheduledAnchorMatchingSet role n m word e).mp he
  have hl' : ∀ h, scheduledBulkLabel role n (e.symm h) = scheduledBulkLabel role n h := by
    intro h
    simpa only [e.apply_symm_apply] using (hl (e.symm h)).symm
  apply (mem_scheduledAnchorMatchingSet role n m word e.symm).mpr
  refine ⟨hl', ?_⟩
  let f := separatedMatchingLeft (scheduledSeparatedMatching role n m word ⟨e, hl⟩)
  let f' := separatedMatchingLeft (scheduledSeparatedMatching role n m word ⟨e.symm, hl'⟩)
  intro x
  have hinv : f (f' x) = x := by
    apply (scheduledBulkCoordinates role n m word).injective
    apply Subtype.ext
    have h := scheduledBulkMatching_slot role n m word ⟨e, hl⟩ (f' x)
    have h' := scheduledBulkMatching_slot role n m word ⟨e.symm, hl'⟩ x
    change e ((scheduledBulkCoordinates role n m word (f' x)).val) =
      (scheduledBulkCoordinates role n m word (f (f' x))).val at h
    change e.symm ((scheduledBulkCoordinates role n m word x).val) =
      (scheduledBulkCoordinates role n m word (f' x)).val at h'
    rw [← h', e.apply_symm_apply] at h
    exact h.symm
  have h := hc (f' x)
  change scheduledBulkAnchorCode n (f (f' x)) = scheduledBulkAnchorCode n (f' x) at h
  rw [hinv] at h
  exact h.symm

theorem scheduled_nonanchor_symm {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (e : Equiv.Perm (CopyScheduleH role n))
    (he : e ∈ cellPreservingMatchings (scheduledBulkLabel role n) \
      scheduledAnchorMatchingSet role n m word) :
    e.symm ∈ cellPreservingMatchings (scheduledBulkLabel role n) \
      scheduledAnchorMatchingSet role n m word := by
  obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp he
  apply Finset.mem_sdiff.mpr
  constructor
  · apply (mem_cellPreservingMatchings _ _).mpr
    intro h
    have hx := ((mem_cellPreservingMatchings _ _).mp hl) (e.symm h)
    simpa only [e.apply_symm_apply] using hx.symm
  · intro h
    exact hn (by simpa only [Equiv.symm_symm] using scheduledAnchorMatchingSet_symm role n m word e.symm h)

end Ostmann

end OAI
