import OAI.Analysis.CircleDomains.Uniformization.ConformalLocalInverse

namespace OAI

/-!
# Images of compact retained cores

A conformal injection on an open neighborhood carries a compact core's
interior and boundary to the interior and boundary of its image. Regular
closed cores remain regular closed. These facts use local openness, not a
boundary extension of the conformal map.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem interior_image_of_continuous_open
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hG : IsOpen G) (hi : InjOn f G) (hKG : K ⊆ G) :
    interior (f '' K) = f '' interior K := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := interior_subset hy
    have hO : IsOpen (G ∩ f ⁻¹' interior (f '' K)) :=
      hc.isOpen_inter_preimage hG isOpen_interior
    have hsub : G ∩ f ⁻¹' interior (f '' K) ⊆ K := by
      rintro z ⟨hzG, hz⟩
      obtain ⟨w, hw, he⟩ := interior_subset hz
      exact (hi (hKG hw) hzG he) ▸ hw
    exact ⟨x, interior_maximal hsub hO ⟨hKG hx, hy⟩, rfl⟩
  · exact interior_maximal (image_mono interior_subset)
      (ho _ isOpen_interior (interior_subset.trans hKG))

theorem interior_image_compact_core
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hf : IsConformalOn f G) (hG : IsOpen G) (hi : InjOn f G)
    (hKG : K ⊆ G) :
    interior (f '' K) = f '' interior K :=
  interior_image_of_continuous_open (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hG hi hKG

theorem frontier_image_of_continuous_open
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hG : IsOpen G) (hi : InjOn f G) (hK : IsCompact K) (hKG : K ⊆ G) :
    frontier (f '' K) = f '' frontier K := by
  have hfc : IsClosed (f '' K) := (hK.image_of_continuousOn (hc.mono hKG)).isClosed
  rw [frontier, hfc.closure_eq, interior_image_of_continuous_open hc ho hG hi hKG,
    frontier, hK.isClosed.closure_eq]
  exact ((hi.mono hKG).image_sdiff_subset interior_subset).symm

theorem frontier_image_compact_core
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hf : IsConformalOn f G) (hG : IsOpen G) (hi : InjOn f G)
    (hK : IsCompact K) (hKG : K ⊆ G) :
    frontier (f '' K) = f '' frontier K :=
  frontier_image_of_continuous_open (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hG hi hK hKG

theorem closure_image_interior_of_continuous
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hf : ContinuousOn f G) (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K) :
    closure (f '' interior K) = f '' K := by
  have hc : ContinuousOn f K := hf.mono hKG
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset) (hK.image_of_continuousOn hc).isClosed
  · have hci : ContinuousOn f (closure (interior K)) := hregular.symm ▸ hc
    simpa only [hregular] using hci.image_closure

theorem closure_image_core_interior
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hf : IsConformalOn f G) (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K) :
    closure (f '' interior K) = f '' K :=
  closure_image_interior_of_continuous (fun p hp => (hf p hp).1.continuousWithinAt)
    hK hKG hregular

end CircleDomainRigidity

end

end OAI
