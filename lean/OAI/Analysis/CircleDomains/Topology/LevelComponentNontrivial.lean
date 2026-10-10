import OAI.Analysis.CircleDomains.Topology.HeightLevelContinuum

namespace OAI

/-! A pointwise level continuum makes the component of the full compact
level section nontrivial. This includes every interior point. -/
open Set Function Filter MeasureTheory Metric Topology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem nontrivial_component_of_continuum
    {K C : Set ℂ} {x : ℂ} (hx : x ∈ K)
    (hc : IsConnected C) (hnt : C.Nontrivial) (hxC : x ∈ C) (hCK : C ⊆ K) :
    (connectedComponent (⟨x, hx⟩ : K)).Nontrivial := by
  let A : Set K := Subtype.val ⁻¹' C
  have him : Subtype.val '' A = C := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hCK]
  have hA : IsPreconnected A := IsInducing.subtypeVal.isPreconnected_image.mp (him ▸ hc.isPreconnected)
  have hsub : A ⊆ connectedComponent (⟨x, hx⟩ : K) := hA.subset_connectedComponent hxC
  apply Set.Nontrivial.mono ?_ hsub
  obtain ⟨a, ha, b, hb, hab⟩ := hnt
  exact ⟨⟨a, hCK ha⟩, ha, ⟨b, hCK hb⟩, hb, fun he => hab (congrArg Subtype.val he)⟩

 theorem height_level_component_nontrivial
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {Q : Set ℂ} {x : ℂ} (hxQ : x ∈ interior Q) :
    (connectedComponent (⟨x, ⟨interior_subset hxQ, rfl⟩⟩ :
      {z : ℂ // z ∈ Q ∧ v z = v x})).Nontrivial := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp hxQ)
  obtain ⟨C, _, hc, hnt, hx, hCb, hlev, _⟩ := height_level_continuum φ hv hlim x hr
  apply nontrivial_component_of_continuum _ hc hnt hx
  intro y hy
  exact ⟨hsub (hCb hy), hlev y hy⟩

end CircleDomainRigidity

end

end OAI
