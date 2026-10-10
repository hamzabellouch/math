import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation

lemma finite_subset_size_image {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (S : Set α) (n : ℕ) :
    (∃ K : Set β, K.Finite ∧ K ⊆ f '' S ∧ n≤K.ncard) ↔
      ∃ K : Set α, K.Finite ∧ K ⊆ S ∧ n≤K.ncard := by
  constructor
  · rintro ⟨K,hK,hKS,hn⟩
    refine ⟨f ⁻¹' K,hK.preimage hf.injOn,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb,heq⟩ := hKS ha
      exact hf heq ▸ hb
    · rwa [Set.ncard_preimage_of_injective_subset_range hf
        (hKS.trans (Set.image_subset_range _ _))]
  · rintro ⟨K,hK,hKS,hn⟩
    exact ⟨f '' K,hK.image f,Set.image_mono hKS,
      (Set.ncard_image_of_injective K hf) ▸ hn⟩

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma induce_clusterTail (S : Set V) (ω : Set (G.inducedEdges S)) (u : S) (n : ℕ) :
    ω ∈ (G.induce S).clusterTail u n ↔
      Subtype.val '' ω ∈ G.clusterTail u.val n := by
  change _ ↔ ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster (Subtype.val '' ω) u.val ∧ n≤K.ncard
  rw [← G.induce_cluster_image]
  exact (finite_subset_size_image Subtype.val Subtype.val_injective _ n).symm

lemma induce_twoClusterEvent (S : Set V) (ω : Set (G.inducedEdges S)) (u v : S) (n : ℕ) :
    ω ∈ (G.induce S).twoClusterEvent u v n ↔
      Subtype.val '' ω ∈ G.twoClusterEvent u.val v.val n := by
  simp only [twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
    G.induce_reachable,G.induce_clusterTail]

lemma restrictVertices_cluster_image (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) (ω : Set E) (u : U) :
    Subtype.val '' ((G.restrictVertices U hU).cluster ω u) = G.cluster ω u.val := by
  ext v
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (G.restrictVertices_reachable U hU ω u a).mp ha
  · intro hv
    have hmem := G.cluster_subset_support U hU u.property hv
    exact ⟨⟨v,hmem⟩,(G.restrictVertices_reachable U hU ω u ⟨v,hmem⟩).mpr hv,rfl⟩

lemma restrictVertices_clusterTail (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) (ω : Set E) (u : U) (n : ℕ) :
    ω ∈ (G.restrictVertices U hU).clusterTail u n ↔ ω ∈ G.clusterTail u.val n := by
  change _ ↔ ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster ω u.val ∧ n≤K.ncard
  rw [← G.restrictVertices_cluster_image U hU ω u]
  exact (finite_subset_size_image Subtype.val Subtype.val_injective _ n).symm

lemma restrictVertices_twoClusterEvent (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) (ω : Set E) (u v : U) (n : ℕ) :
    ω ∈ (G.restrictVertices U hU).twoClusterEvent u v n ↔ ω ∈ G.twoClusterEvent u.val v.val n := by
  simp only [twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
    G.restrictVertices_reachable,G.restrictVertices_clusterTail]

lemma induce_law_event (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (A : Set (Set E)) :
    ((G.induce S).law p).real {ω | Subtype.val '' ω ∈ A} =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ A} := by
  simpa only [law,← BernoulliProduct.law_const] using
    (BernoulliProduct.real_law_restrict p (G.inducedEdges S) hS A).symm

lemma induce_twoCluster_real (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (u v : S) (n : ℕ) :
    ((G.induce S).law p).real ((G.induce S).twoClusterEvent u v n) =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ G.twoClusterEvent u.val v.val n} := by
  have he : (G.induce S).twoClusterEvent u v n =
      {ω | Subtype.val '' ω ∈ G.twoClusterEvent u.val v.val n} := by
    ext ω
    exact G.induce_twoClusterEvent S ω u v n
  rw [he,G.induce_law_event S hS]

end BondGraph
end CriticalPercolation
end
end
end

end OAI
