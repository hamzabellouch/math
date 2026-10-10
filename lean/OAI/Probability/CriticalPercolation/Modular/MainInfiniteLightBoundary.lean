import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyUniqueness
import OAI.Probability.CriticalPercolation.Modular.LightClusterNumber
import OAI.Probability.CriticalPercolation.Modular.MainLightBoundary

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_infinite_light_or_sparse_boundary [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (o : V)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    (¬G.CombinatoriallyUnimodular ∧
      (∀ᵐ ω ∂G.law G.criticalProbability, G.infinitelyManyLightClusters ω) ∧
      (∀ᵐ ω ∂G.law G.criticalProbability, ω∈G.atMostOneHeavy o)) ∨
    (G.SubexponentialGrowth ∧ ∃ d : ℕ, 2≤d ∧
      ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) := by
  rcases G.main_light_or_sparse_polynomial_boundary hc hl hq hpc o hper with ⟨hu,v,hv⟩|hpoly
  · exact Or.inl ⟨hu,G.infinitely_many_light_ae_of_positive hc hl hq G.criticalProbability o v hv,
      G.atMostOneHeavy_critical_ae hc hl hq hpc o⟩
  · exact Or.inr hpoly

end CriticalPercolation.BondGraph
end
end

end OAI
