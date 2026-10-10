import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.Criticality.CriticalFragility
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma restrictEdges_percolates (S : Set E) :
    (fun η : Set E => (Subtype.val ⁻¹' η : Set S)) ⁻¹'
      (G.restrictEdges S).percolates=G.thinPercolatesEvent S := by
  ext η
  simp only [Set.mem_preimage,percolates,thinPercolatesEvent,Set.mem_ofPred_eq,
    cluster,G.restrictEdges_openGraph]

lemma law_restrictEdges (S : Set E) (p : unitInterval) :
    (G.law p).map (fun η : Set E => (Subtype.val ⁻¹' η : Set S))=
      (G.restrictEdges S).law p := by
  simpa only [law,BernoulliProduct.law_const] using
    BernoulliProduct.law_map_restrict (fun _ : E => p) S

lemma law_restrictEdges_percolates [Countable V] [Countable E]
    (S : Set E) (p : unitInterval) :
    (G.restrictEdges S).law p (G.restrictEdges S).percolates=
      G.law p (G.thinPercolatesEvent S) := by
  rw [←G.law_restrictEdges S p,Measure.map_apply,
    G.restrictEdges_percolates]
  · exact Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  · exact (G.restrictEdges S).measurableSet_percolates

lemma intrinsic_critical_eq_one_of_thinning_null [Countable V] [Countable E]
    (ω : Set E) (hω : ∀ r : unitInterval, r<1 →
      G.law r (G.thinPercolatesEvent ω)=0) :
    (G.restrictEdges ω).criticalProbability=1 := by
  apply le_antisymm le_top
  apply le_sInf
  intro p hp
  by_contra hn
  have hlt : p<1 := lt_of_not_ge hn
  have hz := hω p hlt
  rw [←G.law_restrictEdges_percolates] at hz
  exact hp.ne' hz

lemma thinPercolatesEvent_mono_configuration {S T : Set E} (hST : S⊆T) :
    G.thinPercolatesEvent S⊆G.thinPercolatesEvent T := by
  intro η hη
  exact G.percolates_mono (Set.inter_subset_inter_left _ hST) hη

theorem critical_subgraph_threshold_one_ae
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ∀ S : Set E, S⊆ω →
      (G.restrictEdges S).criticalProbability=1 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  filter_upwards [G.critical_thinning_null_ae hc hl] with ω hω
  intro S hS
  apply G.intrinsic_critical_eq_one_of_thinning_null S
  intro r hr
  exact measure_mono_null (G.thinPercolatesEvent_mono_configuration hS) (hω r hr)

theorem critical_open_graph_threshold_one_ae
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) :
    ∀ᵐ ω ∂G.law G.criticalProbability, (G.restrictEdges ω).criticalProbability=1 :=
  (G.critical_subgraph_threshold_one_ae hc hl).mono (fun _ h => h _ Set.Subset.rfl)

end CriticalPercolation.BondGraph
end
end

end OAI
