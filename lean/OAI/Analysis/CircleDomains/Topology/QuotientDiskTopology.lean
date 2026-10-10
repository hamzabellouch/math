import OAI.Analysis.CircleDomains.Topology.SphereNeighborhoods

namespace OAI

/-!
# Topology of projected physical disks

Physical Jordan disks with boundary in the original domain have saturated
interiors and saturated closures. Their images are open with connected
complements, and disjoint physical closed disks give disjoint quotient closed
disks. These properties allow finite dust covers to be used in the descending
grid construction without postulating a disk-selection lemma.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem isConnected_sphere_compl_jordanInterior (H : ℂ ≃ₜ ℂ) :
    IsConnected ((((↑) : ℂ → Sphere) '' jordanInterior H)ᶜ) := by
  have heq : H.onePointCongr '' (((↑) : ℂ → Sphere) '' Metric.ball (0 : ℂ) 1) =
      ((↑) : ℂ → Sphere) '' jordanInterior H := by
    rw [image_image, jordanInterior, image_image]
    rfl
  rw [← heq, ← H.onePointCongr.image_compl]
  exact (isConnected_sphere_exterior_ball (0 : ℂ) zero_lt_one).image _
    H.onePointCongr.continuous.continuousOn

theorem preimage_image_closure_of_singleton_boundary_fibers
    {X Y : Type*} [TopologicalSpace X]
    (π : X → Y) (hfibers : ∀ y, IsPreconnected (π ⁻¹' {y}))
    {U : Set X} (hU : IsOpen U)
    (hsing : ∀ p ∈ frontier U, ∀ q, π q = π p → q = p) :
    π ⁻¹' (π '' closure U) = closure U := by
  have hsat := preimage_image_open_of_singleton_boundary_fibers π hfibers hU hsing
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, hpq⟩
    by_cases hpU : p ∈ U
    · apply subset_closure
      rw [← hsat]
      exact ⟨p, hpU, hpq⟩
    · have hpfront : p ∈ frontier U := by
        rw [hU.frontier_eq]
        exact ⟨hp, hpU⟩
      have hqp : q = p := hsing p hpfront q hpq.symm
      simpa only [hqp] using hp
  · exact subset_preimage_image π (closure U)

theorem preimage_image_closed_jordanInterior_of_component_collapse
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior H))) =
      ((↑) : ℂ → Sphere) '' closure (jordanInterior H) := by
  rw [← closure_sphere_image_jordanInterior]
  apply preimage_image_closure_of_singleton_boundary_fibers π
    (fun y => (connected_fibers_of_component_collapse G π hsurj hr y).isPreconnected)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
  intro p hp q hqp
  rw [frontier_sphere_image_jordanInterior] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rcases (hr (z : Sphere) q).mp hqp.symm with heq | ⟨hznot, _⟩
  · exact heq.symm
  · exact (hznot (hboundary z hz)).elim

theorem image_compl_of_saturated {X Y : Type*} (π : X → Y) (hsurj : Surjective π)
    {U : Set X} (hsat : π ⁻¹' (π '' U) = U) : π '' Uᶜ = (π '' U)ᶜ := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩ hy
    apply hp
    rw [← hsat]
    exact hy
  · intro hy
    obtain ⟨p, rfl⟩ := hsurj y
    refine ⟨p, ?_, rfl⟩
    exact fun hp => hy (mem_image_of_mem _ hp)

theorem isConnected_compl_image_jordanInterior_of_component_collapse
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    IsConnected (π '' (((↑) : ℂ → Sphere) '' jordanInterior H))ᶜ := by
  rw [← image_compl_of_saturated π hsurj
    (preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary)]
  exact (isConnected_sphere_compl_jordanInterior H).image π hπ.continuousOn

/-- Disjointness descends for saturated physical closed fills. -/
theorem disjoint_images_of_saturated {X Y : Type*} (π : X → Y) {A B : Set X}
    (hsat : π ⁻¹' (π '' A) = A) (hd : Disjoint A B) :
    Disjoint (π '' A) (π '' B) := by
  apply Set.disjoint_left.mpr
  rintro y hy ⟨b, hb, hby⟩
  have hbA : b ∈ A := by
    rw [← hsat]
    change π b ∈ π '' A
    exact hby.symm ▸ hy
  exact Set.disjoint_left.mp hd hbA hb

theorem physical_preimage_image_jordanInterior
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    (fun z : ℂ => π (z : Sphere)) ⁻¹'
      (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) = jordanInterior H := by
  change ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹'
    (π '' (((↑) : ℂ → Sphere) '' jordanInterior H))) = _
  rw [preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary,
    Set.preimage_image_eq _ OnePoint.coe_injective]

theorem closure_image_jordanInterior
    {Y : Type*} [TopologicalSpace Y] (π : Sphere → Y)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (H : ℂ ≃ₜ ℂ) :
    closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior H)) := by
  rw [hclosed.closure_image_eq_of_continuous hπ, closure_sphere_image_jordanInterior]

theorem infty_notMem_closure_image_jordanInterior
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π OnePoint.infty ∉ closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  rw [closure_image_jordanInterior π hπ hclosed H]
  intro h
  have hmem : OnePoint.infty ∈ ((↑) : ℂ → Sphere) '' closure (jordanInterior H) := by
    rw [← preimage_image_closed_jordanInterior_of_component_collapse
      G π hsurj hr H hboundary]
    exact h
  obtain ⟨z, _, hz⟩ := hmem
  exact (OnePoint.coe_ne_infty z) hz

end CircleDomainRigidity

end OAI
