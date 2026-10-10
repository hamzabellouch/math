import OAI.Analysis.CircleDomains.Probability.ArcNullImage
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Along a simple arc, domain points are dense when the complementary
dust is totally disconnected. -/

open Set Function
open scoped Topology
namespace CircleDomainRigidity

theorem simple_arc_domain_preimage_dense
    {X : Type*} [TopologicalSpace X] {U B : Set X}
    (hB : IsTotallyDisconnected B) (hBU : Bᶜ ⊆ U)
    (γ : unitInterval → X) (hγ : Continuous γ) (hinj : Injective γ) :
    Dense (γ ⁻¹' U) := by
  apply dense_of_exists_between
  intro a b hab
  by_contra hn
  push Not at hn
  have hsub : γ '' Ioo a b ⊆ B := by
    rintro z ⟨t, ht, rfl⟩
    by_contra htB
    exact hn t (hBU htB) ht
  have hsingle := hB (γ '' Ioo a b) hsub
    (isPreconnected_Ioo.image γ hγ.continuousOn)
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  obtain ⟨d, hcd, hdb⟩ := exists_between hcb
  have heq : γ c = γ d := hsingle ⟨c, ⟨hac, hcb⟩, rfl⟩
    ⟨d, ⟨hac.trans hcd, hdb⟩, rfl⟩
  exact hcd.ne (hinj heq)

theorem simple_arc_point_mem_closure_domain
    {X : Type*} [TopologicalSpace X] {U B : Set X}
    (hB : IsTotallyDisconnected B) (hBU : Bᶜ ⊆ U)
    (γ : unitInterval → X) (hγ : Continuous γ) (hinj : Injective γ) (t : unitInterval) :
    γ t ∈ closure (range γ ∩ U) := by
  have hd := simple_arc_domain_preimage_dense hB hBU γ hγ hinj
  have ht : t ∈ closure (γ ⁻¹' U) := by rw [hd.closure_eq]; trivial
  have him := image_closure_subset_closure_image hγ ⟨t, ht, rfl⟩
  apply closure_mono (fun z hz => ?_) him
  obtain ⟨s, hs, rfl⟩ := hz
  exact ⟨mem_range_self s, hs⟩

end CircleDomainRigidity

end OAI
