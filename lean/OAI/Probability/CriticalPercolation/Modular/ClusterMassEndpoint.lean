import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.Criticality.ExhaustionEvents
import OAI.Probability.CriticalPercolation.Modular.ClusterMassRestriction
import OAI.Probability.CriticalPercolation.Modular.ClusterMassEndpointFinite

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma restrict_edgeDiscrepancy_eq {K ω : Set E} (e : K)
    (hx : G.incidentEdges (G.cluster ω (G.ends e.val).out.1) ⊆ K)
    (hy : G.incidentEdges (G.cluster ω (G.ends e.val).out.2) ⊆ K)
    (s : ℕ) (p : ℝ) :
    edgeDiscrepancy (G.restrictEdges K) s p (Subtype.val ⁻¹' ω) e =
      edgeDiscrepancy G s p ω e.val := by
  have hc := cluster_inter_eq G hx
  have hconn : ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)).Reachable
      (G.ends e.val).out.1 (G.ends e.val).out.2 ↔
        (G.openGraph ω).Reachable (G.ends e.val).out.1 (G.ends e.val).out.2 := by
    rw [G.restrictEdges_openGraph]
    exact Set.ext_iff.mp hc _
  unfold edgeDiscrepancy edgeMass size coefficient
  change (if e.val ∈ ω then -(1-p)/p else 1) *
    (cappedMass s ((G.restrictEdges K).cluster (Subtype.val ⁻¹' ω) (G.ends e.val).out.1).ncard +
      (if ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)).Reachable (G.ends e.val).out.1 (G.ends e.val).out.2 then 0
       else cappedMass s ((G.restrictEdges K).cluster (Subtype.val ⁻¹' ω) (G.ends e.val).out.2).ncard)) = _
  rw [hconn,restrict_cluster,restrict_cluster,cluster_inter_eq G hx,cluster_inter_eq G hy]

lemma restrict_twoCluster (K : Set E) (ω : Set E) (u v : V) (s : ℕ) :
    Subtype.val ⁻¹' ω ∈ (G.restrictEdges K).twoClusterEvent u v s ↔
      K ∩ ω ∈ G.twoClusterEvent u v s := by
  simp only [BondGraph.twoClusterEvent,Set.mem_inter_iff,BondGraph.clusterTail,
    Set.mem_ofPred_eq,restrict_cluster,G.restrictEdges_openGraph]

variable [Countable V] [Countable E]

lemma restrict_twoCluster_real (p : unitInterval) (K : Set E) (u v : V) (s : ℕ) :
    ((G.restrictEdges K).law p).real ((G.restrictEdges K).twoClusterEvent u v s) =
      (G.law p).real {ω | K ∩ ω ∈ G.twoClusterEvent u v s} := by
  simp only [BondGraph.law,← BernoulliProduct.law_const]
  rw [← BernoulliProduct.law_map_restrict (fun _ : E => p) K]
  simp only [measureReal_def]
  rw [Measure.map_apply (measurable_restrict K)
    ((G.restrictEdges K).measurableSet_twoClusterEvent u v s)]
  congr 2
  ext ω
  exact restrict_twoCluster G K ω u v s

lemma restricted_edgeDiscrepancy_integral (p : unitInterval) (K : Set E) (e : K) (s : ℕ) :
    (∫ ω, edgeDiscrepancy (G.restrictEdges K) s p (Subtype.val ⁻¹' ω) e ∂G.law p) =
      ∫ ω, edgeDiscrepancy (G.restrictEdges K) s p ω e ∂(G.restrictEdges K).law p := by
  simp only [BondGraph.law,← BernoulliProduct.law_const]
  rw [← BernoulliProduct.law_map_restrict (fun _ : E => p) K]
  rw [integral_map (measurable_restrict K).aemeasurable
    (measurable_edgeDiscrepancy (G.restrictEdges K) s p e).aestronglyMeasurable]

theorem subcritical_endpoint_le_integral (hl : G.LocallyFinite)
    (s : ℕ) (hs : 0<s) (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1)
    (hpc : p < G.criticalProbability) (e : E) :
    (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s) ≤
      ∫ ω, edgeDiscrepancy G s p ω e ∂G.law p := by
  let K₀ := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let K : Set.FiniteExhaustion (Set.univ : Set E) :=
    { toFun := fun n => insert e (K₀ n)
      finite' := fun n => (K₀.finite n).insert e
      subset_succ' := fun n => Set.insert_subset_insert (K₀.subset_succ n)
      iUnion_eq' := by
        apply Set.eq_univ_of_forall
        intro a
        obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (K₀.iUnion_eq.symm ▸ Set.mem_univ a)
        exact Set.mem_iUnion.mpr ⟨n,Or.inr hn⟩ }
  let en (n : ℕ) : K n := ⟨e,Or.inl rfl⟩
  let F := fun n ω => edgeDiscrepancy (G.restrictEdges (K n)) s p (Subtype.val ⁻¹' ω) (en n)
  have hb (n : ℕ) : (G.law p).real {ω | K n ∩ ω ∈
      G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s} ≤ ∫ ω, F n ω ∂G.law p := by
    rw [← restrict_twoCluster_real G p (K n),show (∫ ω, F n ω ∂G.law p) = _ from
      restricted_edgeDiscrepancy_integral G p (K n) (en n) s]
    let := (K.finite n).fintype
    exact finite_endpoint_le_integral (G.restrictEdges (K n)) s hs p hp (en n)
  have ht : Tendsto (fun n => ∫ ω, F n ω ∂G.law p) atTop
      (𝓝 (∫ ω, edgeDiscrepancy G s p ω e ∂G.law p)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 2/(p:ℝ))
    · intro n
      exact ((measurable_edgeDiscrepancy (G.restrictEdges (K n)) s p (en n)).comp
        (measurable_restrict (K n))).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro ω
      exact edgeDiscrepancy_abs_le (G.restrictEdges (K n)) s hp _ (en n)
    · filter_upwards [ae_finite_clusters G p hpc] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_incident_subset G hl K (hω (G.ends e).out.1),
        eventually_incident_subset G hl K (hω (G.ends e).out.2)] with n hn hm
      exact (restrict_edgeDiscrepancy_eq G (en n) hn hm s p).symm
  exact le_of_tendsto_of_tendsto (G.tendsto_real_twoCluster_restrict p _ _ s K) ht
    (Eventually.of_forall hb)

end CriticalPercolation.FiniteClusters
end
end

end OAI
