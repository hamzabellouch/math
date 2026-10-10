import OAI.Analysis.CircleDomains.Transfer.FiniteChartConnectivity

namespace OAI

/-!
# Smooth physical disks from the component quotient

These statements combine compact clopen isolation, actual contour selection,
the component quotient, and the infinity-chart argument. Connectedness and
unboundedness of the physical exterior are conclusions of the preceding
lemmas, not additional disk-selection hypotheses.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- Concrete finite smooth Jordan disks covering the physical fiber of `x`.
The indexing set is a finite subset of the regular level's components. -/
def SmoothPhysicalDiskCover {X : Type*} (π : Sphere → X) (x : X)
    (V F : Set X) (G : Set Sphere) : Prop :=
  ∃ (f : ℂ → ℝ) (t : ℝ)
    (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
    (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
    (s : Set (ConnectedComponents {z // f z = t})),
    s.Finite ∧
    (∀ z : ℂ, π (z : Sphere) = x → z ∈ ⋃ i ∈ s, jordanInterior (H i)) ∧
    s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
      (closure (jordanInterior (H j)))) ∧
    (∀ i ∈ s, closure (jordanInterior (H i)) ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
    ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
      Topology.IsEmbedding (γ i) ∧ frontier (jordanInterior (H i)) = range (γ i) ∧
      (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F)

/-- The small physical disk construction for a singleton component of
the actual quotient obstacle. -/
theorem smoothPhysicalDiskCover_of_component_quotient
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    SmoothPhysicalDiskCover π x V F G := by
  obtain ⟨hphysical, hunbounded⟩ :=
    physical_exterior_connected_unbounded_of_component_collapse G π hπ hclosed hsurj hr
      hV hVconn hinfty
  exact exists_small_physical_disks_at_singleton_component hsard hschoenflies
    π hπ hF hx hcomponent hV hxV (fun h => hinfty (subset_closure h))
      hphysical hunbounded hbad

/-- Adjoining the quotient dust preserves singleton components and the
resulting smooth boundaries avoid both the original obstacle and dust. -/
theorem smoothPhysicalDiskCover_after_adjoining_dust
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F B V : Set X} (hF : IsClosed F) (hB : IsClosed B)
    (hTD : IsTotallyDisconnected B) {x : X} (hx : x ∈ F ∪ B)
    (hsing : x ∈ F → connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) :
    SmoothPhysicalDiskCover π x V (F ∪ B) G := by
  apply smoothPhysicalDiskCover_of_component_quotient hsard hschoenflies
    G π hπ hclosed hsurj hr (hF.union hB) hx
    (component_union_dust_eq_singleton hF hB hTD hx hsing) hV hxV hVconn hinfty
  intro p hp
  exact Or.inr (hbad p hp)

end CircleDomainRigidity

end OAI
