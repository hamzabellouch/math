import Mathlib.Topology.Connected.Basic

namespace OAI

/-! Transport of a connected component through an embedding, used for
the finite chart in the sphere. -/
open Set Function Topology
noncomputable section
namespace CircleDomainRigidity

lemma embedding_image_connectedComponentIn {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f:X→Y} (hf:IsEmbedding f) {S:Set X} {x:X} (hx:x∈S) :
    f '' connectedComponentIn S x=connectedComponentIn (f '' S) (f x) := by
  apply Subset.antisymm (hf.continuous.continuousOn.image_connectedComponentIn_subset hx)
  let K := connectedComponentIn (f '' S) (f x)
  have hKsub : K⊆range f := (connectedComponentIn_subset _ _).trans (image_subset_range _ _)
  have he : f '' (f ⁻¹' K)=K := image_preimage_eq_of_subset hKsub
  have hpre : IsPreconnected (f ⁻¹' K) := hf.isInducing.isPreconnected_image.mp (by
    rw [he]
    exact isPreconnected_connectedComponentIn)
  have hxm : x∈f ⁻¹' K := mem_connectedComponentIn (mem_image_of_mem f hx)
  have hsub : f ⁻¹' K⊆S := by
    intro z hz
    obtain ⟨w,hw,heq⟩ := connectedComponentIn_subset (f '' S) (f x) hz
    exact hf.injective heq ▸ hw
  change K⊆f '' connectedComponentIn S x
  rw [←he]
  exact image_mono (hpre.subset_connectedComponentIn hxm hsub)

end CircleDomainRigidity

end

end OAI
