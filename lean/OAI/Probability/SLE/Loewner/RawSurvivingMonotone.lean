import OAI.Probability.SLE.Loewner.TargetCutoffTrajectory

namespace OAI

/-! Raw survival decreases with the time horizon. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge.Target

lemma surviving_of_le_time (κ : ℝ) (b : Driver) (z : ℂ) {S T : ℝ}
    (hS : 0 ≤ S) (hST : S ≤ T) (h : Surviving κ b z T) : Surviving κ b z S := by
  obtain ⟨j,hj,hmin⟩ := h
  refine ⟨j,hj,hmin.trans_le ?_⟩
  have hc : IsCompact ((fun t : ℝ => (cutoffFlow κ b j z t).im) '' Icc 0 T) :=
    isCompact_Icc.image_of_continuousOn (Complex.continuous_im.comp_continuousOn
      ((cutoffFlow_continuousOn κ b j hj z).mono Icc_subset_Ici_self))
  apply le_csInf (Set.Nonempty.image _ (nonempty_Icc.mpr hS))
  rintro y ⟨s,hs,rfl⟩
  exact csInf_le hc.bddBelow ⟨s,⟨hs.1,hs.2.trans hST⟩,rfl⟩

end SLEExactGauge.Target

end

end OAI
