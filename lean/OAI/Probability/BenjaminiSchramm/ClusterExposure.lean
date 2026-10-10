import OAI.Probability.BenjaminiSchramm.BlockExposure
import OAI.Probability.CriticalPercolation.Clusters.ClusterObject
import OAI.Probability.CriticalPercolation.Clusters.ComponentSelf

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exactCluster_dependsOn (x : V) (S : Set V) :
    DependsOn (fun ω : Set E => G.cluster ω x = S) (G.incidentEdges S) := by
  intro ω η hω
  apply propext
  have hforward (ω η : Set E) (hωη : ∀ e ∈ G.incidentEdges S, e ∈ ω ↔ e ∈ η)
      (hS : G.cluster ω x = S) : G.cluster η x = S := by
    have hr : ClusterDeletion.roots (G.openGraph ω) {x} = S := by
      simpa only [ClusterDeletion.roots_singleton, ClusterDeletion.component, cluster] using hS
    have hr' := G.roots_eq_of_incident hr hωη
    simpa only [ClusterDeletion.roots_singleton, ClusterDeletion.component, cluster] using hr'
  exact ⟨hforward ω η (fun e he => (hω e he).to_iff),
    hforward η ω (fun e he => (hω e he).symm.to_iff)⟩

lemma measurable_eraseVertices (S : Set V) : Measurable (fun ω => G.eraseVertices ω S) := by
  refine (@measurable_pi_iff (Set E) E (fun _ => Prop)
    inferInstance (fun _ => inferInstance) _).mpr ?_
  intro e
  exact (measurable_set_mem e).and measurable_const

lemma measurableSet_exactCluster [Countable V] [Countable E] (x : V) (S : Set V) :
    MeasurableSet {ω | G.cluster ω x = S} := by
  have heq : {ω | G.cluster ω x = S} =
      ⋂ y : V, {ω | (G.openGraph ω).Reachable x y ↔ y ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Set.ext_iff
  rw [heq]
  exact MeasurableSet.iInter fun y => ((G.measurable_reachable x y).iff measurable_const).setOf

theorem exactCluster_exterior_factor [Countable V] [Countable E]
    (p : unitInterval) (x : V) (S : Set V) (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, ({ω | G.cluster ω x = S} : Set (Set E)).indicator
      (fun ω => F (G.eraseVertices ω S)) ω ∂G.law p) =
        G.law p {ω | G.cluster ω x = S} *
          ∫⁻ η, F (G.eraseVertices η S) ∂G.law p := by
  unfold law
  rw [← BernoulliProduct.law_const]
  apply BernoulliProduct.lintegral_indicator_fresh (fun _ => p) (G.incidentEdges S)
    _ (G.measurableSet_exactCluster x S) (G.exactCluster_dependsOn x S)
    _ (hF.comp (G.measurable_eraseVertices S))
  intro ω η hωη
  exact congrArg F (G.eraseVertices_dependsOn S hωη)

lemma exactCluster_exterior_le [Countable V] [Countable E]
    (p : unitInterval) (x : V) (S : Set V) (F : Set E → ℝ≥0∞) (hF : Measurable F)
    (B : ℝ≥0∞) (hB : (∫⁻ η, F (G.eraseVertices η S) ∂G.law p) ≤ B) :
    (∫⁻ ω, ({ω | G.cluster ω x = S} : Set (Set E)).indicator
      (fun ω => F (G.eraseVertices ω S)) ω ∂G.law p) ≤
        G.law p {ω | G.cluster ω x = S} * B := by
  rw [G.exactCluster_exterior_factor p x S F hF]
  exact mul_le_mul' le_rfl hB

end CriticalPercolation.BondGraph

end

end OAI
