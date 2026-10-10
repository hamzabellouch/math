import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas

namespace OAI

/-! Exact transport of components and componentwise-constant functions
under a homeomorphism, used in the recursive shrinking construction. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma embedding_image_componentIn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsEmbedding f) {F : Set X} {x : X} (hx : x ∈ F) :
    f '' connectedComponentIn F x = connectedComponentIn (f '' F) (f x) := by
  apply Subset.antisymm (hf.continuous.continuousOn.image_connectedComponentIn_subset hx)
  have hr : connectedComponentIn (f '' F) (f x) ⊆ range f :=
    (connectedComponentIn_subset _ _).trans (image_subset_range _ _)
  have hp : IsPreconnected (f ⁻¹' connectedComponentIn (f '' F) (f x)) := by
    apply hf.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset hr]
    exact isPreconnected_connectedComponentIn
  have hsub : f ⁻¹' connectedComponentIn (f '' F) (f x) ⊆ F := by
    intro y hy
    obtain ⟨z,hz,he⟩ := connectedComponentIn_subset _ _ hy
    exact hf.injective he ▸ hz
  have hc := hp.subset_connectedComponentIn
    (mem_connectedComponentIn (mem_image_of_mem f hx)) hsub
  intro y hy
  obtain ⟨z,rfl⟩ := hr hy
  exact ⟨z,hc hy,rfl⟩

lemma homeomorph_image_componentIn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) {F : Set X} {x : X} (hx : x ∈ F) :
    H '' connectedComponentIn F x = connectedComponentIn (H '' F) (H x) := by
  apply Subset.antisymm (H.continuous.continuousOn.image_connectedComponentIn_subset hx)
  intro y hy
  have hs := H.symm.continuous.continuousOn.mapsTo_connectedComponentIn
    (mem_image_of_mem H hx) hy
  have he : H.symm '' (H '' F)=F := H.toEquiv.symm_image_image F
  rw [he,H.symm_apply_apply] at hs
  exact ⟨H.symm y,hs,H.apply_symm_apply y⟩

lemma component_constant_transport
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) {F : Set X} (q : X → Z)
    (hq : ∀ x ∈ F, ∀ y ∈ connectedComponentIn F x, q y=q x) :
    ∀ x ∈ H '' F, ∀ y ∈ connectedComponentIn (H '' F) x,
      q (H.symm y)=q (H.symm x) := by
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := hx
  rw [← homeomorph_image_componentIn H ha] at hy
  obtain ⟨b,hb,rfl⟩ := hy
  simpa only [H.symm_apply_apply] using hq a ha b hb

end CircleDomainRigidity

end

end OAI
