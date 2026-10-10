import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseC2Stability

namespace OAI

/-! A fixed compact family of immersed jets with nonzero second form has
a positive second-form margin throughout one uniform C2 neighborhood. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma isOpen_secondFormMargin (c : ℝ) : IsOpen
    {J : RealTwoJet | NormalFrame.gramDet (J 0) (J 1) ≠ 0 ∧ c < ‖secondTensorFromJet J‖} := by
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hd : Continuous (fun K : RealTwoJet => NormalFrame.gramDet (K 0) (K 1)) := by
    unfold NormalFrame.gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_secondTensorFromJet hJ.1).continuousAt.norm.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds hJ.2))

theorem compact_secondForm_margin {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {K : Set Base} (hK : IsCompact K)
    (hI : ∀ p ∈ K, Function.Injective (fderiv ℝ F p))
    (hB : ∀ p ∈ K, realSecondTensor F p ≠ 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ G : RField 4,
      (∀ p ∈ K, ‖realTwoJet G p-realTwoJet F p‖ < ε) →
      ∀ p ∈ K, Function.Injective (fderiv ℝ G p) ∧ c < ‖realSecondTensor G p‖ := by
  let Q := realTwoJet F '' K
  have hQ : IsCompact Q := hK.image (contDiff_realTwoJet hF).continuous
  have hD : ∀ J ∈ Q, NormalFrame.gramDet (J 0) (J 1) ≠ 0 := by
    rintro J ⟨p,hp,rfl⟩
    exact gramDet_ne_zero_of_injective _ (hI p hp)
  have hN : ∀ J ∈ Q, 0 < ‖secondTensorFromJet J‖ := by
    rintro J ⟨p,hp,rfl⟩
    exact norm_pos_iff.mpr (hB p hp)
  by_cases hQne : Q.Nonempty
  · have hcont : ContinuousOn (fun J => ‖secondTensorFromJet J‖) Q :=
      fun J hJ => ((contDiffAt_secondTensorFromJet (hD J hJ)).continuousAt.norm).continuousWithinAt
    obtain ⟨J,hJ,hmin⟩ := hQ.exists_isMinOn hQne hcont
    let c := ‖secondTensorFromJet J‖/2
    have hc : 0 < c := half_pos (hN J hJ)
    have hsub : Q ⊆ {H : RealTwoJet |
        NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖secondTensorFromJet H‖} := by
      intro H hH
      exact ⟨hD H hH,(half_lt_self (hN J hJ)).trans_le (hmin hH)⟩
    obtain ⟨ε,hε,he⟩ := hQ.exists_thickening_subset_open (isOpen_secondFormMargin c) hsub
    refine ⟨ε,c,hε,hc,?_⟩
    intro G hGF p hp
    have hmem := he (Metric.mem_thickening_iff.mpr
      ⟨realTwoJet F p,mem_image_of_mem _ hp,by simpa only [dist_eq_norm] using hGF p hp⟩)
    exact ⟨injective_of_gramDet_ne_zero _ hmem.1,hmem.2⟩
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro G _ p hp
    exact False.elim (hQne ⟨realTwoJet F p,mem_image_of_mem _ hp⟩)

theorem compact_secondForm_C2_margin {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {K : Set Base} (hK : IsCompact K)
    (hI : ∀ p ∈ K, Function.Injective (fderiv ℝ F p))
    (hB : ∀ p ∈ K, realSecondTensor F p ≠ 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ G : RField 4, ContDiff ℝ ∞ G →
      ∀ b : ℝ, 0 ≤ b → b < ε → WeightedBound univ 1 2 b (G-F) →
      ∀ p ∈ K, Function.Injective (fderiv ℝ G p) ∧ c < ‖realSecondTensor G p‖ := by
  obtain ⟨ε,c,hε,hc,he⟩ := compact_secondForm_margin hF hK hI hB
  refine ⟨ε,c,hε,hc,?_⟩
  intro G hG b hb hbε hclose
  apply he G
  intro p _
  have hh := norm_realTwoJet_le (hG.sub hF) hb hclose p
  change ‖realTwoJet (G-F) p‖ ≤ b at hh
  rw [realTwoJet_sub hG hF] at hh
  exact hh.trans_lt hbε

end ClosedSurfaceR4.RealModes

end

end OAI
