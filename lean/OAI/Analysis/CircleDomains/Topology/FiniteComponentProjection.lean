import OAI.Analysis.CircleDomains.Topology.ComponentQuotientModel
import OAI.Analysis.CircleDomains.Transfer.FiniteChartConnectivity
import OAI.Analysis.CircleDomains.Topology.HomeomorphComponentTransport

namespace OAI

/-! The finite coordinate complement and its actual component projection. -/
open Set Function
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma finite_complement_image {G : Set Sphere} (hi : ∞ ∈ G) :
    ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' Gᶜ) = Gᶜ := by
  apply image_preimage_eq_of_subset
  intro x hx
  cases x using OnePoint.rec with
  | infty => exact (hx hi).elim
  | coe z => exact ⟨z,rfl⟩

lemma finite_complement_connected {G : Set Sphere}
    (hG : IsOpen G) (hc : IsConnected G) (hi : ∞ ∈ G) :
    IsConnected ((((↑) : ℂ → Sphere) ⁻¹' Gᶜ)ᶜ) := by
  obtain ⟨hp,hu⟩ := finite_part_connected_unbounded hc.isPreconnected
    (hG.interior_eq.symm ▸ hi)
  have hn : (((↑) : ℂ → Sphere) ⁻¹' G).Nonempty := by
    by_contra h
    exact hu (Set.not_nonempty_iff_eq_empty.mp h ▸ Bornology.isBounded_empty)
  simpa only [preimage_compl,compl_compl] using (show IsConnected (((↑) : ℂ → Sphere) ⁻¹' G) from ⟨hn,hp⟩)

lemma finite_componentProjection_constant {G : Set Sphere}
    (x : ℂ) (hx : (x : Sphere) ∈ Gᶜ) {y : ℂ}
    (hy : y ∈ connectedComponentIn (((↑) : ℂ → Sphere) ⁻¹' Gᶜ) x) :
    componentProjection G (y : Sphere)=componentProjection G (x : Sphere) := by
  apply Eq.symm
  apply (componentProjection_eq G _ _).mpr
  refine Or.inr ⟨hx,?_⟩
  exact connectedComponentIn_mono _ (image_preimage_subset _ _)
    ((OnePoint.continuous_coe (X := ℂ)).continuousOn.image_connectedComponentIn_subset
      (s := ((↑) : ℂ → Sphere) ⁻¹' Gᶜ) hx
      (mem_image_of_mem _ hy))

lemma finite_component_membership {G : Set Sphere} (hi : ∞ ∈ G)
    {x y : ℂ} (hx : (x : Sphere) ∈ Gᶜ)
    (hy : (y : Sphere) ∈ connectedComponentIn Gᶜ (x : Sphere)) :
    y ∈ connectedComponentIn (((↑) : ℂ → Sphere) ⁻¹' Gᶜ) x := by
  have he := embedding_image_componentIn (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding
    (F := ((↑) : ℂ → Sphere) ⁻¹' Gᶜ) hx
  rw [finite_complement_image hi] at he
  rw [← he] at hy
  obtain ⟨z,hz,hzy⟩ := hy
  exact OnePoint.coe_injective hzy ▸ hz

end CircleDomainRigidity

end

end OAI
