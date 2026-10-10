import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.MainResidualBoundary
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyUniqueness

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma critical_twoHeavyDistinct_null (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hp1 : G.criticalProbability<1) (o x y : V) :
    G.law G.criticalProbability (G.twoHeavyDistinctEvent o x y)=0 := by
  have h := G.atMostOneHeavy_critical_ae hc hl hq hp1 o
  have hh : ∀ᵐ ω ∂G.law G.criticalProbability, ω∉G.twoHeavyDistinctEvent o x y := by
    filter_upwards [h] with ω hω ⟨⟨hx,hy⟩,hnot⟩
    exact hnot (hω x y hx hy)
  rw [ae_iff] at hh
  simpa only [not_not,Set.ofPred_mem_eq] using hh

theorem main_light_or_sparse_polynomial_boundary [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (o : V)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    (¬G.CombinatoriallyUnimodular ∧
      ∃ v, 0<G.law G.criticalProbability (G.lightInfiniteEvent o v)) ∨
    (G.SubexponentialGrowth ∧ ∃ d : ℕ, 2≤d ∧
      ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) := by
  rcases G.main_residual_boundary hc hl hq hpc o hper with ⟨hu,hlight|hheavy⟩|hsparse
  · exact Or.inl ⟨hu,hlight⟩
  · obtain ⟨x,y,hxy⟩ := hheavy
    rw [G.critical_twoHeavyDistinct_null hc hl hq hpc o x y] at hxy
    exact False.elim ((lt_irrefl _) hxy)
  · exact Or.inr hsparse

end CriticalPercolation.BondGraph
end
end

end OAI
