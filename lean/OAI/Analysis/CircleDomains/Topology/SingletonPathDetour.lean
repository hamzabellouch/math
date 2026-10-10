import OAI.Analysis.CircleDomains.Topology.SingletonDetourNeighborhood

namespace OAI

/-! A path whose contacts with a closed level all belong to singleton
components can be deformed off that level, inside its prescribed open
mask. The small neighborhoods come from the actual component quotient. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_path_avoiding_singleton_level
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B H V : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hH : IsClosed H) (hV : IsOpen V)
    (hinfty : π OnePoint.infty ∉ V)
    {x y : Sphere} (hx : x ∉ H) (hy : y ∉ H) (γ : Path x y)
    (hγV : range γ ⊆ V)
    (hsing : ∀ z ∈ range γ ∩ H, connectedComponentIn H z = {z}) :
    ∃ δ : Path x y, range δ ⊆ V ∧ Disjoint (range δ) H := by
  apply exists_path_avoiding_from_local_boundary_detours γ hH hγV
  intro z hz
  let W : Set Sphere := V ∩ ({x, y} : Set Sphere)ᶜ
  have hxy : IsClosed ({x, y} : Set Sphere) := by
    simpa only [singleton_union] using
      (isClosed_singleton.union isClosed_singleton : IsClosed ({x} ∪ {y} : Set Sphere))
  have hW : IsOpen W := hV.inter hxy.isOpen_compl
  have hzW : z ∈ W := by
    refine ⟨hγV hz.1, ?_⟩
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun he => hx (he ▸ hz.2), fun he => hy (he ▸ hz.2)⟩
  obtain ⟨N, hN, hzN, hNW, hNc⟩ := exists_sphere_neighborhood_connected_compl hW hzW
  have hNinf : π OnePoint.infty ∉ closure N := fun hn => hinfty (hNW hn).1
  have hs : connectedComponentIn (H ∪ B) z = {z} :=
    component_union_dust_eq_singleton hH hB hTD (Or.inl hz.2) (fun _ => hsing z hz)
  obtain ⟨U, hU, hzU, hUN, hbU, hmU⟩ := exists_singleton_detour_neighborhood
    hsard hsch G π hπ hclosed hsurj hr (hH.union hB) (Or.inl hz.2)
    hs hN hzN hNc hNinf (fun p hp => Or.inr (hbad p hp))
  have hUW : closure U ⊆ W := hUN.trans (subset_closure.trans hNW)
  refine ⟨U, hU, hzU, fun a ha => (hUW ha).1, ?_, ?_, hbU,
    hmU.mono_right subset_union_left⟩
  · intro hxU
    exact (hUW hxU).2 (by simp)
  · intro hyU
    exact (hUW hyU).2 (by simp)

end CircleDomainRigidity

end

end OAI
