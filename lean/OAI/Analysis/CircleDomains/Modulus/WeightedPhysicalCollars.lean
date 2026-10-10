import OAI.Analysis.CircleDomains.Modulus.WeightedJordanCovers
import OAI.Analysis.CircleDomains.Topology.SinglePhysicalDisk

namespace OAI

/-! Finite-cost smooth physical collars of an actual collapsed component.
The regular level containing the chosen boundary is retained explicitly. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_small_physical_disk
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (f : ℂ → ℝ) (t : ℝ),
      {z : ℂ | π (z : Sphere) = x} ⊆ jordanInterior H ∧
      closure (jordanInterior H) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      frontier (jordanInterior H) ⊆ {z | f z = t} ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ IsPlanarRegularValue f t ∧
      {z | f z = t} ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      (∀ z, f z = t → (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) ∧
      (∫⁻z in {z | f z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
  classical
  obtain ⟨hphysical, hunbounded⟩ :=
    physical_exterior_connected_unbounded_of_component_collapse G π hπ hclosed hsurj hr
      hV hVconn hinfty
  obtain ⟨A, hAc, hxA, hAF, hAV, hFA⟩ :=
    exists_compact_piece_of_singleton_component hF hx hcomponent hV hxV
  let q : ℂ → X := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hAp : IsCompact (q ⁻¹' A) := by
    apply isCompact_finite_preimage (hAc.isClosed.preimage hπ)
    exact fun h => hinfty (subset_closure (hAV h))
  have hFp : IsClosed ((q ⁻¹' F) \ (q ⁻¹' A)) := by
    simpa only [preimage_sdiff] using hFA.preimage hq
  obtain ⟨f, t, γ, H, s, hf, hreg, hlevelV, havoid, hcost,
    _, hcov, hd, hinside, hcurves⟩ :=
    exists_finite_weighted_jordan_cover hcoarea hsard hschoenflies hAp
      (preimage_mono hAF) hFp (hV.preimage hq) (preimage_mono hAV)
      hphysical hunbounded g hg hg2
  have hfiber : IsConnected {z : ℂ | π (z : Sphere) = x} := by
    apply isConnected_finite_fiber π (connected_fibers_of_component_collapse G π hsurj hr)
    intro heq
    exact hinfty (subset_closure (heq.symm ▸ hxV))
  have hpair : Pairwise (Disjoint on fun i : s => jordanInterior (H i)) := by
    intro i j hij
    exact (hd i.property j.property (fun h => hij (Subtype.ext h))).mono
      subset_closure subset_closure
  have hcover : {z : ℂ | π (z : Sphere) = x} ⊆ ⋃ i : s, jordanInterior (H i) := by
    intro z hz
    have hzA : z ∈ q ⁻¹' A := by
      change π (z : Sphere) ∈ A
      rwa [hz]
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hzA)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨i, hi⟩ := exists_member_containing_connected_set hfiber
    (fun i : s => jordanInterior (H i)) (fun i => jordanInterior_isOpen (H i)) hpair hcover
  obtain ⟨hγ, hemb, hfront, _, hfrontlevel⟩ := hcurves i i.property
  refine ⟨H i, γ i, f, t, hi, hinside i i.property, hγ, hemb, hfront,
    hfrontlevel, hf, hreg, hlevelV, ?_, hcost⟩
  intro z hz
  have hnot : π (z : Sphere) ∉ F := fun h => disjoint_left.mp havoid hz h
  refine ⟨?_, hnot⟩
  by_contra h
  exact hnot (hbad _ h)

end CircleDomainRigidity

end

end OAI
