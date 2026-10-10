import OAI.Analysis.CircleDomains.Topology.SaturatedFrontier
import OAI.Analysis.CircleDomains.Topology.JordanDiskImages
import OAI.Analysis.CircleDomains.Uniformization.MobiusConformal

namespace OAI

/-! The actual image of a physical collar under the component-collapse map
is a Jordan disk. Its filled side is identified by its exact frontier. -/

open Set Function Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem continuousOn_finiteCoord_of_avoids_infty {S : Set Sphere}
    (hS : OnePoint.infty ∉ S) : ContinuousOn finiteCoord S := by
  apply OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff.mpr
  apply continuousOn_id.congr
  intro x hx
  change (finiteCoord x : Sphere) = x
  exact CannonMobius.coe_coordinate (fun h => hS (h ▸ hx))

theorem exists_jordan_quotient_collar (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    (hinf : OnePoint.infty ∉ closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior H))) :
    ∃ K : ℂ ≃ₜ ℂ,
      π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
        ((↑) : ℂ → Sphere) '' jordanInterior K := by
  let W := ((↑) : ℂ → Sphere) '' jordanInterior H
  let V := π '' W
  have hW : IsOpen W := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hV : IsOpen V := isOpen_image_jordanInterior_of_component_collapse
    G π hπ hclosed hsurj hr H hboundary
  have hWc : IsCompact (closure W) := by
    rw [closure_sphere_image_jordanInterior]
    exact (isCompact_closure_jordanInterior H).image OnePoint.continuous_coe
  have hsat : π ⁻¹' V = W := preimage_image_jordanInterior_of_component_collapse
    G π hsurj hr H hboundary
  have hfront : frontier V = π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := by
    rw [frontier_image_of_saturated_open π hπ W hW hV (hWc.image hπ).isClosed hsat,
      frontier_sphere_image_jordanInterior]
  let c : Circle → Sphere := fun t => π ((H (t : ℂ) : ℂ) : Sphere)
  have hc : Continuous c := hπ.comp (OnePoint.continuous_coe.comp
    (H.continuous.comp continuous_subtype_val))
  have hrange : range c = frontier V := by
    rw [hfront, frontier_jordanInterior]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨_, ⟨t, t.property, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hcf (t : Circle) : c t ≠ OnePoint.infty := by
    intro he
    apply hinf
    rw [← he]
    exact frontier_subset_closure (hrange ▸ mem_range_self t)
  have hci : Injective c := by
    intro s t he
    have hsG : ((H (s : ℂ) : ℂ) : Sphere) ∈ G :=
      hboundary _ (by rw [frontier_jordanInterior]; exact ⟨s, s.property, rfl⟩)
    rcases (hr _ _).mp he with h | h
    · exact Subtype.ext (H.injective (OnePoint.coe_injective h))
    · exact (h.1 hsG).elim
  let δ : Circle → ℂ := finiteCoord ∘ c
  have hδ : Continuous δ :=
    (continuousOn_finiteCoord_of_avoids_infty hinf).comp_continuous hc
      (fun t => frontier_subset_closure (hrange ▸ mem_range_self t))
  have hδi : Injective δ := by
    intro s t h
    apply hci
    have h' := congrArg ((↑) : ℂ → Sphere) h
    change (finiteCoord (c s) : Sphere) = (finiteCoord (c t) : Sphere) at h'
    exact (CannonMobius.coe_coordinate (hcf s)).symm.trans
      (h'.trans (CannonMobius.coe_coordinate (hcf t)))
  obtain ⟨K, hK⟩ := hsch δ hδ hδi
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' V
  have hAf : frontier A = range δ := by
    rw [← OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
      OnePoint.continuous_coe V, ← hrange]
    ext z
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change finiteCoord (c t) = z
      rw [ht, finiteCoord_coe]
    · rintro ⟨t, rfl⟩
      exact ⟨t, (CannonMobius.coe_coordinate (hcf t)).symm⟩
  have hAn : A.Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_jordanInterior H).nonempty
    have hx : π (z : Sphere) ∈ V := ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hxne : π (z : Sphere) ≠ OnePoint.infty := fun h => hinf (h ▸ subset_closure hx)
    exact ⟨finiteCoord (π (z : Sphere)), (CannonMobius.coe_coordinate hxne).symm ▸ hx⟩
  have hAK : A = jordanInterior K := open_eq_jordanInterior_of_frontier K
    (hV.preimage OnePoint.continuous_coe)
    ((isCompact_finite_preimage isClosed_closure hinf).isBounded.subset
      (preimage_mono subset_closure)) hAn
    (hAf.trans (frontier_jordanInterior_eq_circle_range K δ hK).symm)
  refine ⟨K, ?_⟩
  change V = ((↑) : ℂ → Sphere) '' jordanInterior K
  rw [← hAK]
  apply Subset.antisymm
  · intro x hx
    have hxne : x ≠ OnePoint.infty := fun h => hinf (h ▸ subset_closure hx)
    exact ⟨finiteCoord x, (CannonMobius.coe_coordinate hxne).symm ▸ hx,
      CannonMobius.coe_coordinate hxne⟩
  · exact image_preimage_subset _ _

end CircleDomainRigidity

end

end OAI
