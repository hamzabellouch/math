import OAI.Analysis.CircleDomains.Topology.QuotientCollarJordan
import OAI.Analysis.CircleDomains.Topology.QuotientDiskTopology
import OAI.Analysis.CircleDomains.Topology.FiniteBoundaryDetour
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace OAI

/-! The existing small physical disk construction supplies actual
quotient neighborhoods with path connected boundaries avoiding the
whole obstacle. These are the neighborhoods used in finite detours. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_singleton_detour_neighborhood
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hsing : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ closure U ⊆ V ∧
      IsPathConnected (frontier U) ∧ Disjoint (frontier U) F := by
  obtain ⟨J, c, hcover, hJV, hc, _, hfront, hboundary⟩ :=
    exists_single_small_physical_disk hsard hsch G π hπ hclosed hsurj hr
      hF hx hsing hV hxV hVconn hinfty hbad
  let W : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  let U : Set X := π '' W
  have hW : IsOpen W := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hU : IsOpen U := isOpen_image_jordanInterior_of_component_collapse
    G π hπ hclosed hsurj hr J (fun z hz => (hboundary z hz).1)
  have hcl : closure U = π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior J)) :=
    closure_image_jordanInterior π hπ hclosed J
  have hsat : π ⁻¹' U = W := preimage_image_jordanInterior_of_component_collapse
    G π hsurj hr J (fun z hz => (hboundary z hz).1)
  have hcW : IsCompact (closure W) := by
    rw [closure_sphere_image_jordanInterior]
    exact (isCompact_closure_jordanInterior J).image OnePoint.continuous_coe
  have hUF : frontier U = π '' (((↑) : ℂ → Sphere) '' range c) := by
    rw [frontier_image_of_saturated_open π hπ W hW hU
      (hcW.image hπ).isClosed hsat,
      frontier_sphere_image_jordanInterior, hfront]
  refine ⟨U, hU, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hsurj x
    cases p using OnePoint.rec with
    | infty => exact False.elim (hinfty (hp.symm ▸ subset_closure hxV))
    | coe z => exact ⟨z, ⟨z, hcover hp, rfl⟩, hp⟩
  · rw [hcl]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hJV hz
  · rw [hUF]
    exact ((isPathConnected_range hc.continuous).image OnePoint.continuous_coe).image hπ
  · rw [hUF]
    apply Set.disjoint_left.mpr
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ hmem
    exact (hboundary z (hfront.symm ▸ hz)).2 hmem

end CircleDomainRigidity

end

end OAI
