import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.Criticality.SubexponentialVolumes

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma induce_locallyFinite (hl : G.LocallyFinite) (S : Set V) : (G.induce S).LocallyFinite := by
  intro v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hl v.val)).subset
  intro e he
  have hh : v.val∈Sym2.map Subtype.val ((G.induce S).ends e) := Sym2.mem_map.mpr ⟨v,he,rfl⟩
  rwa [G.induce_ends_map] at hh

lemma induce_fullGraph_adj (S : Set V) (x y : S) :
    (G.induce S).fullGraph.Adj x y → G.fullGraph.Adj x.val y.val := by
  intro h
  exact G.openGraph_mono (Set.subset_univ _) ((G.induce_adj S Set.univ x y).mp h)

lemma induce_vertexBall_subset (S : Set V) (o : S) (n : ℕ) :
    Subtype.val '' (G.induce S).vertexBall o n ⊆ G.vertexBall o.val n := by
  induction n with
  | zero => rintro x ⟨y,rfl,rfl⟩; rfl
  | succ n ih =>
    rintro x ⟨y,hy,rfl⟩
    rcases hy with hy|hy
    · exact G.vertexBall_mono o.val (Nat.le_succ n) (ih ⟨y,hy,rfl⟩)
    · obtain ⟨z,hz,hzy⟩ := Set.mem_iUnion₂.mp hy
      exact G.vertexBall_step (ih ⟨z,hz,rfl⟩) (G.induce_fullGraph_adj S z y hzy)

lemma induce_subexponential (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth) (S : Set V) :
    (G.induce S).SubexponentialGrowth := by
  intro o ε hε
  obtain ⟨N,hN⟩ := hg o.val ε hε
  refine ⟨N,fun n hn => ?_⟩
  have hcard : ((G.induce S).vertexBall o n).ncard ≤ (G.vertexBall o.val n).ncard := by
    rw [←Set.ncard_image_of_injective _ Subtype.val_injective]
    exact Set.ncard_le_ncard (G.induce_vertexBall_subset S o n) (G.vertexBall_finite hl o.val n)
  have hpositive : 0<(((G.induce S).vertexBall o n).ncard : ℝ) := by
    exact_mod_cast (Set.ncard_pos ((G.induce S).vertexBall_finite (G.induce_locallyFinite hl S) o n)).mpr
      ⟨o,(G.induce S).mem_vertexBall_self o n⟩
  exact (Real.log_le_log hpositive (by exact_mod_cast hcard)).trans (hN n hn)

lemma induce_percolates_subset (S : Set V) :
    (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set (G.inducedEdges S)) ⁻¹' (G.induce S).percolates
      ⊆G.percolates := by
  rintro ω ⟨o,ho⟩
  refine ⟨o.val,?_⟩
  have hi := ho.image Subtype.val_injective.injOn
  rw [G.induce_cluster_image] at hi
  exact hi.mono (G.cluster_mono (by rintro e ⟨a,ha,rfl⟩; exact ha) o.val)

lemma law_induce [Countable V] [Countable E] (S : Set V) (p : unitInterval) :
    (G.law p).map (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set (G.inducedEdges S)) =
      (G.induce S).law p := by
  simpa only [law,BernoulliProduct.law_const] using
    BernoulliProduct.law_map_restrict (fun _ : E => p) (G.inducedEdges S)

lemma law_induce_percolates_le [Countable V] [Countable E] (S : Set V) (p : unitInterval) :
    (G.induce S).law p (G.induce S).percolates ≤ G.law p G.percolates := by
  rw [←G.law_induce S p,Measure.map_apply]
  · exact measure_mono (G.induce_percolates_subset S)
  · exact Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  · exact (G.induce S).measurableSet_percolates

lemma criticalProbability_le_induce [Countable V] [Countable E] (S : Set V) :
    G.criticalProbability≤(G.induce S).criticalProbability := by
  apply le_sInf
  intro p hp
  exact G.criticalProbability_le_of_pos (hp.trans_le (G.law_induce_percolates_le S p))

lemma induce_criticalProbability_eq_of_pos [Countable V] [Countable E] (S : Set V)
    (hpos : 0<(G.induce S).law G.criticalProbability (G.induce S).percolates) :
    (G.induce S).criticalProbability=G.criticalProbability :=
  le_antisymm ((G.induce S).criticalProbability_le_of_pos hpos) (G.criticalProbability_le_induce S)

end CriticalPercolation.BondGraph
end
end
end

end OAI
