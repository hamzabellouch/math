import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.Modular.ClusterMassFinite

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_inter_eq {ω K : Set E} {v : V}
    (h : G.incidentEdges (G.cluster ω v) ⊆ K) :
    G.cluster (K ∩ ω) v = G.cluster ω v := by
  apply Set.Subset.antisymm (fun _ hr => hr.mono (G.openGraph_mono inter_subset_right))
  intro w hw
  rw [BondGraph.cluster,Set.mem_ofPred_eq,SimpleGraph.reachable_iff_reflTransGen] at hw ⊢
  induction hw with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u w hu huw ih =>
    apply ih.tail
    obtain ⟨⟨e,he,hend⟩,hne⟩ := huw
    refine ⟨⟨e,⟨h ?_,he⟩,hend⟩,hne⟩
    exact ⟨u,((G.openGraph ω).reachable_iff_reflTransGen _ _).mpr hu,by rw [hend]; simp⟩

lemma restrict_cluster (K : Set E) (ω : Set E) (v : V) :
    (G.restrictEdges K).cluster (Subtype.val ⁻¹' ω) v = G.cluster (K ∩ ω) v := by
  simp only [BondGraph.cluster,G.restrictEdges_openGraph]

lemma restrict_incident (K : Set E) (S : Set V) :
    (G.restrictEdges K).incidentEdges S = Subtype.val ⁻¹' (G.incidentEdges S) := rfl

lemma restrict_local (hl : G.LocallyFinite) (K : Set E) : (G.restrictEdges K).LocallyFinite := by
  intro v
  change (Subtype.val ⁻¹' {e : E | v ∈ G.ends e} : Set K).Finite
  exact (hl v).preimage Subtype.val_injective.injOn

lemma restrict_incident_bound (hl : G.LocallyFinite) (K : Set E) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) (v : V) :
    ((G.restrictEdges K).incidentEdges {v}).ncard ≤ D := by
  rw [restrict_incident]
  exact (Set.ncard_le_ncard_of_injOn Subtype.val (fun _ h => h)
    Subtype.val_injective.injOn (G.finite_incident hl (Set.finite_singleton v))).trans (hD v)

lemma restrict_rootSum_eq {K ω : Set E} {v : V}
    (h : G.incidentEdges (G.cluster ω v) ⊆ K) (p : ℝ) :
    rootSum (G.restrictEdges K) p (Subtype.val ⁻¹' ω) v = rootSum G p ω v := by
  unfold rootSum
  rw [restrict_cluster,cluster_inter_eq G h,restrict_incident]
  change (∑' e : K, if e.val ∈ G.incidentEdges (G.cluster ω v) then coefficient p ω e.val else 0) = _
  apply tsum_subtype_eq_of_support_subset (s := K)
    (f := fun e => if e ∈ G.incidentEdges (G.cluster ω v) then coefficient p ω e else 0)
  intro e he
  by_contra hn
  have hi : e ∉ G.incidentEdges (G.cluster ω v) := fun hi => hn (h hi)
  exact he (ite_eq_right hi)

lemma restrict_rootAbsolute_eq {K ω : Set E} {v : V}
    (h : G.incidentEdges (G.cluster ω v) ⊆ K) (s : ℕ) (p : ℝ) :
    rootAbsolute (G.restrictEdges K) s p (Subtype.val ⁻¹' ω) v = rootAbsolute G s p ω v := by
  rw [rootAbsolute,restrict_rootSum_eq G h]
  unfold rootAbsolute mass size
  rw [restrict_cluster,cluster_inter_eq G h]

lemma eventually_incident_subset (hl : G.LocallyFinite)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) {ω : Set E} {v : V}
    (hC : (G.cluster ω v).Finite) : ∀ᶠ n in atTop, G.incidentEdges (G.cluster ω v) ⊆ K n := by
  have hi := G.finite_incident hl hC
  have hh (e : E) : ∀ᶠ n in atTop, e ∈ K n := by
    have : e ∈ ⋃ n, K n := by rw [K.iUnion_eq]; trivial
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp this
    exact eventually_atTop.mpr ⟨n,fun m hm => K.mono hm hn⟩
  exact (eventually_all_finite hi).mpr (fun e _ => hh e)

variable [Countable V] [Countable E]

omit [Countable E] in
lemma measurable_restrict (K : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) :=
  Measurable.of_eval (fun edge => measurable_set_mem edge.val)

lemma restricted_rootAbsolute_integral (p : unitInterval) (K : Set E) (hK : K.Finite)
    (s : ℕ) (v : V) :
    (∫ ω, rootAbsolute (G.restrictEdges K) s p (Subtype.val ⁻¹' ω) v ∂G.law p) =
    ∫ ω, rootAbsolute (G.restrictEdges K) s p ω v ∂(G.restrictEdges K).law p := by
  let := hK.fintype
  simp only [BondGraph.law,← BernoulliProduct.law_const]
  rw [← BernoulliProduct.law_map_restrict (fun _ : E => p) K]
  rw [integral_map (measurable_restrict K).aemeasurable
    (measurable_rootAbsolute (G.restrictEdges K) s p v).aestronglyMeasurable]

omit [Countable V] [Countable E] in
lemma ae_finite_clusters (p : unitInterval) (hp : p < G.criticalProbability) :
    ∀ᵐ ω ∂G.law p, ∀ v, (G.cluster ω v).Finite := by
  have hh := G.law_percolates_eq_zero_of_lt_critical hp
  rw [measure_eq_zero_iff_ae_notMem] at hh
  filter_upwards [hh] with ω hω v
  exact not_not.mp (fun hc => hω ⟨v,hc⟩)

theorem subcritical_rootAbsolute_bound (hl : G.LocallyFinite)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability)
    (k : ℕ) (v : V) :
    (∫ ω, rootAbsolute G (4^k) p ω v ∂G.law p) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
  let : IsProbabilityMeasure (G.law p) := by
    unfold BondGraph.law
    infer_instance
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let F := fun n ω => rootAbsolute (G.restrictEdges (K n)) (4^k) p (Subtype.val ⁻¹' ω) v
  have hb (n : ℕ) : (∫ ω, F n ω ∂G.law p) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
    rw [show (∫ ω, F n ω ∂G.law p) = _ from
      restricted_rootAbsolute_integral G p (K n) (K.finite n) (4^k) v]
    let := (K.finite n).fintype
    exact finite_rootAbsolute_integral (G.restrictEdges (K n)) p hp D hDpos
      (restrict_incident_bound G hl (K n) D hD) k v
  have ht : Tendsto (fun n => ∫ ω, F n ω ∂G.law p) atTop
      (𝓝 (∫ ω, rootAbsolute G (4^k) p ω v ∂G.law p)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (D:ℝ)/(p:ℝ))
    · intro n
      exact ((measurable_rootAbsolute (G.restrictEdges (K n)) (4^k) p v).comp
        (measurable_restrict (K n))).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro ω
      dsimp only [F]
      rw [Real.norm_eq_abs,abs_of_nonneg (rootAbsolute_nonneg _ _ _ _ _)]
      exact rootAbsolute_bound (G.restrictEdges (K n)) (restrict_local G hl (K n)) D
        (restrict_incident_bound G hl (K n) D hD) (4^k) hp _ v
    · filter_upwards [ae_finite_clusters G p hpc] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_incident_subset G hl K (hω v)] with n hn
      exact (restrict_rootAbsolute_eq G hn (4^k) p).symm
  exact le_of_tendsto ht (Eventually.of_forall hb)

end CriticalPercolation.FiniteClusters
end
end

end OAI
