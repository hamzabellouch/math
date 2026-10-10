import OAI.Analysis.CircleDomains.Sobolev.SmoothContours

namespace OAI

/-! A bounded region whose boundary lies in an open smooth locus admits
a cutoff whose transitions stay in that locus and preserve a strict range bound. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_range_preserving_cutoff
    {D O : Set ℂ} (hD : IsOpen D) (hO : IsOpen O)
    (hK : IsCompact (closure O)) (hfront : frontier O ⊆ D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) {b : ℝ}
    (hbound : ∀ z ∈ closure O, z ∈ D → f z < b) :
    ∃ η : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      (∀ z, η z ∈ Icc 0 1) ∧ (∀ᶠ z in 𝓝ˢ (closure O), η z = 1) ∧
      (∀ z, z ∉ D → fderiv ℝ η z = 0) ∧
      (∀ z ∈ D, η z ≠ 0 → f z ≤ b) := by
  let V := D ∩ f ⁻¹' Iio b
  have hV : IsOpen V := hf.isOpen_inter_preimage hD isOpen_Iio
  have hsub : closure O ⊆ O ∪ V := by
    intro z hz
    by_cases hi : z ∈ O
    · exact Or.inl hi
    · have hd : z ∈ D := hfront ⟨hz, by simpa only [hO.interior_eq] using hi⟩
      exact Or.inr ⟨hd, hbound z hz hd⟩
  obtain ⟨η, hη, hs, hsupp, hunit, hone⟩ :=
    exists_smooth_planar_cutoff hK (hO.union hV) hsub
  refine ⟨η, hη, hs, hunit, hone, ?_, ?_⟩
  · intro z hzD
    by_cases hz : z ∈ closure O
    · have hlocal : η =ᶠ[𝓝 z] fun _ => (1 : ℝ) := hone.filter_mono (nhds_le_nhdsSet hz)
      rw [hlocal.fderiv_eq]
      exact fderiv_const_apply 1
    · apply fderiv_of_notMem_tsupport ℝ
      intro h
      rcases hsupp h with ho | hv
      · exact hz (subset_closure ho)
      · exact hzD hv.1
  · intro z hzD hzη
    rcases hsupp (subset_tsupport η hzη) with ho | hv
    · exact (hbound z (subset_closure ho) hzD).le
    · exact hv.2.le

end CircleDomainRigidity

end

end OAI
