import OAI.Analysis.CircleDomains.Modulus.WeightedCollarNeighborhoods

namespace OAI

/-! The actual projected Jordan collars have connected complements and
their closed regions miss the image of physical infinity. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem isConnected_sphere_jordan_exterior (H : ℂ ≃ₜ ℂ) :
    IsConnected ((((↑) : ℂ → Sphere) '' jordanInterior H)ᶜ) := by
  have hi : (H.onePointCongr : Sphere → Sphere) ''
      (((↑) : ℂ → Sphere) '' Metric.ball (0 : ℂ) 1) =
      ((↑) : ℂ → Sphere) '' jordanInterior H := by
    rw [image_image, jordanInterior, image_image]
    rfl
  rw [← hi, ← H.onePointCongr.image_compl]
  exact (isConnected_sphere_exterior_ball 0 zero_lt_one).image _ H.onePointCongr.continuous.continuousOn

namespace WeightedCollar

variable {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere}
  {p : Sphere} {g : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g)

theorem isConnected_compl_region (hπ : Continuous π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsConnected D.regionᶜ := by
  let S : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior D.disk
  have hsat : π ⁻¹' (π '' S) = S := preimage_image_jordanInterior_of_component_collapse
    G π hsurj hr D.disk (fun z hz => (D.level_good z (D.frontier_level hz)).1)
  have heq : π '' Sᶜ = D.regionᶜ := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩ hx
      exact hz (hsat ▸ hx)
    · intro hx
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z, fun hz => hx ⟨z, hz, rfl⟩, rfl⟩
  rw [← heq]
  exact (isConnected_sphere_jordan_exterior D.disk).image π hπ.continuousOn

theorem infty_notMem_closure_region (hπ : Continuous π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    π OnePoint.infty ∉ closure D.region := by
  intro hinfty
  obtain ⟨_, ⟨z, hz, rfl⟩, heq⟩ := D.closure_region_subset_image hπ hinfty
  have hsat := preimage_image_jordanInterior_of_component_collapse
    G π hsurj hr D.disk (fun z hz => (D.level_good z (D.frontier_level hz)).1)
  have hznot : z ∉ jordanInterior D.disk := by
    intro hzin
    have hi : π OnePoint.infty ∈ D.region := heq ▸ ⟨(z : Sphere), ⟨z, hzin, rfl⟩, rfl⟩
    have hi' : OnePoint.infty ∈ π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior D.disk)) := hi
    rw [hsat] at hi'
    exact OnePoint.infty_notMem_image_coe hi'
  have hzfront : z ∈ frontier (jordanInterior D.disk) := by
    rw [(jordanInterior_isOpen D.disk).frontier_eq]
    exact ⟨hz, hznot⟩
  rcases (hr (z : Sphere) OnePoint.infty).mp heq with h | ⟨h, _⟩
  · exact OnePoint.coe_ne_infty z h
  · exact h (D.level_good z (D.frontier_level hzfront)).1

end WeightedCollar
end CircleDomainRigidity

end

end OAI
