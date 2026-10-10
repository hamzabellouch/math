import OAI.Analysis.CircleDomains.Sobolev.InverseChartCoarea

namespace OAI

/-! Each regular point has a neighborhood on all of whose Borel subsets
weighted coarea holds. Bounding the image keeps the line parameters bounded. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal Topology ContDiff Classical
noncomputable section
namespace CircleDomainRigidity

lemma isOpen_planar_regular {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    IsOpen (D ∩ {z | fderiv ℝ f z ≠ 0}) :=
  (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).isOpen_inter_preimage
    hD isClosed_singleton.isOpen_compl

lemma exists_regular_coarea_neighborhood {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {x : ℂ} (hx : x ∈ D)
    (hr : fderiv ℝ f x ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ U ⊆ D ∩ {z | fderiv ℝ f z ≠ 0} ∧
      ∀ S : Set ℂ, MeasurableSet S → S ⊆ U →
        ∀ q : ℂ → ℝ≥0∞, Measurable q → WeightedScalarCoareaIdentity S f q := by
  obtain ⟨e, hxe, heD, he, heC, heI⟩ := exists_complex_c1_level_chart hD hf hx hr
  let U := (e.source ∩ e ⁻¹' ball (e x) 1) ∩ (D ∩ {z | fderiv ℝ f z ≠ 0})
  have hU : IsOpen U :=
    (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).inter (isOpen_planar_regular hD hf)
  refine ⟨U, hU, ⟨⟨hxe, mem_ball_self (by norm_num)⟩, hx, hr⟩, inter_subset_right, ?_⟩
  intro S hS hSU q hq
  have hSe : S ⊆ e.source := fun z hz => (hSU hz).1.1
  have hT : MeasurableSet (e '' S) :=
    hS.image_of_continuousOn_injOn (heC.continuousOn.mono hSe) (e.injOn.mono hSe)
  have hb : IsBounded (e '' S) := isBounded_ball.subset (by
    rintro y ⟨z, hz, rfl⟩
    exact (hSU hz).1.2)
  have hTe : e '' S ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hSe hz)
  have h := inverse_chart_weighted_coarea hD hf e heD he heI hT hb hTe hq
  have heq : e.symm '' (e '' S) = S := by
    exact e.toPartialEquiv.symm_image_image_of_subset_source hSe
  rwa [heq] at h

end CircleDomainRigidity

end

end OAI
