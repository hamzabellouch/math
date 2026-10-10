import OAI.Probability.SLE.Loewner.TargetCutoffTrajectory

namespace OAI

/-! A surviving raw trajectory continues for a strictly longer time.
This follows directly from the strict cutoff-height certificate. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology

namespace SLEExactGauge.Target

theorem exists_later_survival (κ : ℝ) (b : Driver) (z : ℂ)
    {T : ℝ} (hT : 0 ≤ T) (hs : Surviving κ b z T) :
    ∃ S : ℝ, T < S ∧ Surviving κ b z S := by
  obtain ⟨j,hj,hmin⟩ := hs
  have hc := cutoffFlow_continuousOn κ b j hj z
  have hh := surviving_cutoff_height κ b z T j hj hmin
  have hTj := hh T ⟨hT,le_rfl⟩
  have he : ∀ᶠ t in 𝓝[Ici 0] T, (j:ℝ)⁻¹ < (cutoffFlow κ b j z t).im :=
    (Complex.continuous_im.comp_continuousOn hc T hT).eventually (Ioi_mem_nhds hTj)
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhdsWithin_iff.mp he
  let S : ℝ := T+δ/2
  have hTS : T < S := by dsimp [S]; linarith
  have hS : 0 ≤ S := hT.trans hTS.le
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 S) :
      (j:ℝ)⁻¹ < (cutoffFlow κ b j z t).im := by
    by_cases htT : t ≤ T
    · exact hh t ⟨ht.1,htT⟩
    · apply hδb
      refine ⟨?_,ht.1⟩
      rw [mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr (lt_of_not_ge htT))]
      have hts := ht.2
      dsimp only [S] at hts
      linarith
  obtain ⟨t,ht,htmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hS)
    (Complex.continuous_im.comp_continuousOn (hc.mono Icc_subset_Ici_self))
  refine ⟨S,hTS,j,hj,(hpoint t ht).trans_le ?_⟩
  apply le_csInf (Set.Nonempty.image _ (nonempty_Icc.mpr hS))
  rintro y ⟨s,hs,rfl⟩
  exact htmin hs

end SLEExactGauge.Target

end

end OAI
