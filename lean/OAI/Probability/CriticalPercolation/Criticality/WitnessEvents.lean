import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation
namespace BernoulliProduct
variable {E : Type*}

lemma tendsto_real_inter_finiteWitness (p : unitInterval) (A B : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law (fun _ : E => p)).real (B ∩ {ω | K n ∩ ω ∈ A}))
      atTop (𝓝 ((law (fun _ : E => p)).real (B∩A))) := by
  have hm : Monotone (fun n => B ∩ {ω | K n ∩ ω ∈ A}) :=
    fun _ _ h => Set.inter_subset_inter_right _ (finiteWitness_exhaustion_mono A hmono K h)
  have h := tendsto_measure_iUnion_atTop (μ := law (fun _ : E => p)) hm
  rw [← Set.inter_iUnion,finiteWitness_exhaustion A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

end BernoulliProduct
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def witnessedTwoCluster (K : Set E) (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.openGraph ω).Reachable u v} ∩
    {ω | K∩ω ∈ G.clusterTail u s ∩ G.clusterTail v s}

lemma witnessedTwoCluster_subset_restrict {K S : Set E} (hKS : K⊆S) (u v : V) (s : ℕ) :
    G.witnessedTwoCluster K u v s ⊆ {ω | S∩ω ∈ G.twoClusterEvent u v s} := by
  rintro ω ⟨hsep,hu,hv⟩
  refine ⟨⟨?_,G.clusterTail_isUpperSet u s (Set.inter_subset_inter_left _ hKS) hu⟩,
    G.clusterTail_isUpperSet v s (Set.inter_subset_inter_left _ hKS) hv⟩
  intro h
  exact hsep (G.cluster_mono Set.inter_subset_right u h)

lemma measurableSet_witnessedTwoCluster [Countable V] [Countable E]
    (K : Set E) (hK : K.Finite) (u v : V) (s : ℕ) :
    MeasurableSet (G.witnessedTwoCluster K u v s) :=
  (G.measurable_reachable u v).setOf.compl.inter
    (BernoulliProduct.measurableSet_restrict K hK _)

lemma tendsto_real_witnessedTwoCluster (p : unitInterval) (u v : V) (s : ℕ)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (G.law p).real (G.witnessedTwoCluster (K n) u v s)) atTop
      (𝓝 ((G.law p).real (G.twoClusterEvent u v s))) := by
  have ht := BernoulliProduct.tendsto_real_inter_finiteWitness p
    (G.clusterTail u s ∩ G.clusterTail v s) {ω | ¬(G.openGraph ω).Reachable u v}
    ((G.clusterTail_isUpperSet u s).inter (G.clusterTail_isUpperSet v s))
    ((G.clusterTail_hasFiniteOpenWitness u s).inter (G.clusterTail_hasFiniteOpenWitness v s)
      (G.clusterTail_isUpperSet u s) (G.clusterTail_isUpperSet v s)) K
  simpa only [witnessedTwoCluster,twoClusterEvent,Set.inter_assoc,law,
    ← BernoulliProduct.law_const] using ht

lemma exists_finite_witnessedTwoCluster [Countable E] (p : unitInterval) (u v : V) (s : ℕ)
    (hpos : 0 < (G.law p).real (G.twoClusterEvent u v s)) :
    ∃ K : Set E, K.Finite ∧ (G.law p).real (G.twoClusterEvent u v s)/2 ≤
      (G.law p).real (G.witnessedTwoCluster K u v s) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  obtain ⟨n,hn⟩ := ((G.tendsto_real_witnessedTwoCluster p u v s K).eventually
    (eventually_gt_nhds (by linarith : (G.law p).real (G.twoClusterEvent u v s)/2 <
      (G.law p).real (G.twoClusterEvent u v s)))).exists
  exact ⟨K n,K.finite n,hn.le⟩

lemma Aut.reachable_map (φ : G.Aut) (ω : Set E) (u v : V) :
    (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex u) (φ.vertex v) ↔
      (G.openGraph ω).Reachable u v :=
  SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)

lemma Aut.clusterTail_map (φ : G.Aut) (ω : Set E) (u : V) (s : ℕ) :
    φ.edge '' ω ∈ G.clusterTail (φ.vertex u) s ↔ ω ∈ G.clusterTail u s := by
  exact Set.ext_iff.mp (Aut.preimage_clusterTail G φ u s) ω

lemma Aut.witnessedTwoCluster_preimage (φ : G.Aut) (K : Set E) (u v : V) (s : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹'
      G.witnessedTwoCluster (φ.edge '' K) (φ.vertex u) (φ.vertex v) s =
        G.witnessedTwoCluster K u v s := by
  ext ω
  simp only [witnessedTwoCluster,Set.mem_preimage,Set.mem_inter_iff,Set.mem_ofPred_eq]
  rw [← Set.image_inter φ.edge.injective,Aut.reachable_map,
    Aut.clusterTail_map,Aut.clusterTail_map]

lemma Aut.witnessedTwoCluster_real [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (K : Set E) (hK : K.Finite) (u v : V) (s : ℕ) :
    (G.law p).real (G.witnessedTwoCluster (φ.edge '' K) (φ.vertex u) (φ.vertex v) s) =
      (G.law p).real (G.witnessedTwoCluster K u v s) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_witnessedTwoCluster _ (hK.image _) _ _ _),
    Aut.witnessedTwoCluster_preimage]

lemma twoClusterEvent_comm (u v : V) (s : ℕ) :
    G.twoClusterEvent u v s = G.twoClusterEvent v u s := by
  ext ω
  simp only [twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h,hu⟩,hv⟩
    exact ⟨⟨fun hc => h hc.symm,hv⟩,hu⟩
  · rintro ⟨⟨h,hv⟩,hu⟩
    exact ⟨⟨fun hc => h hc.symm,hu⟩,hv⟩

lemma twoClusterEvent_sym2 {u v x y : V} (h : s(u,v)=s(x,y)) (s : ℕ) :
    G.twoClusterEvent u v s = G.twoClusterEvent x y s := by
  rcases Sym2.eq_iff.mp h with h | h
  · rcases h with ⟨rfl,rfl⟩; rfl
  · rcases h with ⟨rfl,rfl⟩; exact G.twoClusterEvent_comm _ _ _

end BondGraph
end CriticalPercolation
end
end
end

end OAI
