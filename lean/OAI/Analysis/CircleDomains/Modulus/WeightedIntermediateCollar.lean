import OAI.Analysis.CircleDomains.Modulus.WeightedAnnularCollars
import OAI.Analysis.CircleDomains.Modulus.WeightedCollarNeighborhoods

namespace OAI

/-! An actual weighted collar between an inner physical Jordan disk and
an outer quotient disk. Its entire joining level stays in the intervening annulus. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_intermediate_collar
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hbad : ∀x ∈ Gᶜ, π x ∈ B)
    {p : Sphere} {g₀ : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g₀)
    {V : Set Sphere} (hV : IsOpen V) (hVc : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hinside : closure (jordanInterior D.disk) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ E : WeightedCollar G π B p g,
      closure D.region ⊆ E.region ∧ closure E.region ⊆ V ∧
      {z | E.function z = E.level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (V \ closure D.region) := by
  let A := closure (jordanInterior D.disk)
  let F := (fun z : ℂ => π (z : Sphere)) ⁻¹' B
  let U := (fun z : ℂ => π (z : Sphere)) ⁻¹' V
  have hq : Continuous (fun z : ℂ => π (z : Sphere)) := hπ.comp OnePoint.continuous_coe
  have hA : IsCompact A := isCompact_closure_jordanInterior D.disk
  have hFA : Disjoint F (frontier A) := by
    apply Set.disjoint_left.mpr
    intro z hzF hzA
    exact (D.level_good z (D.frontier_level (frontier_closure_subset hzA))).2 hzF
  obtain ⟨hUconn, hUun⟩ := physical_exterior_connected_unbounded_of_component_collapse
    G π hπ hclosed hsurj hr hV hVc hinfty
  obtain ⟨H, γ, f, t, hAH, hHV, hγ, hemb, hfront, hfrontlevel,
    hf, hreg, hlevel, hcost⟩ := exists_weighted_collar_around_compact
      hcoarea hsard hsch hA (isConnected_jordanInterior D.disk).closure
      (hB.preimage hq) hFA (hV.preimage hq) hinside hUconn hUun g hg hg2
  have hgood (z : ℂ) (hz : f z = t) : (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B := by
    have hnot : π (z : Sphere) ∉ B := fun h => (hlevel hz).2 (Or.inr h)
    refine ⟨?_, hnot⟩
    by_contra h
    exact hnot (hbad _ h)
  let E : WeightedCollar G π B p g :=
    ⟨H, γ, f, t, D.fiber_inside.trans (subset_closure.trans hAH),
      hγ, hemb, hfront, hfrontlevel, hf, hreg, hgood, hcost⟩
  refine ⟨E, ?_, E.closure_region_subset hπ hHV, ?_⟩
  · intro x hx
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := D.closure_region_subset_image hπ hx
    exact ⟨(z : Sphere), ⟨z, hAH hz, rfl⟩, rfl⟩
  · intro z hz
    refine ⟨(hlevel hz).1, ?_⟩
    intro hx
    obtain ⟨_, ⟨u, hu, rfl⟩, heq⟩ := D.closure_region_subset_image hπ hx
    have hzu : (z : Sphere) = (u : Sphere) := by
      rcases (hr (z : Sphere) (u : Sphere)).mp heq.symm with h | ⟨h, _⟩
      · exact h
      · exact (h ((hgood z hz).1)).elim
    have hzu' : z = u := OnePoint.coe_injective hzu
    exact (hlevel hz).2 (Or.inl (hzu'.symm ▸ hu))

end CircleDomainRigidity

end

end OAI
