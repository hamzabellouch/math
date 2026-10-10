import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.LayerContradiction
import OAI.Probability.CriticalPercolation.Modular.MainAllLightBoundary

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_failure_sparse_polynomial [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    G.SubexponentialGrowth ∧ G.CombinatoriallyUnimodular ∧
      ∃ d : ℕ, 2≤d ∧ ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d := by
  have hu : G.CombinatoriallyUnimodular := by
    by_contra hn
    exact hper (G.nonunimodular_no_percolation_at_criticality hc hl hq hn hpc)
  obtain ⟨o⟩ := hc.nonempty
  rcases G.main_all_light_or_sparse_boundary hc hl hq hpc o hper with ⟨hn,_⟩|⟨hg,hpoly⟩
  · exact False.elim (hn hu)
  · exact ⟨hg,hu,hpoly⟩

theorem non_subexponential_no_percolation_at_criticality [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (hg : ¬G.SubexponentialGrowth) :
    G.law G.criticalProbability G.percolates=0 := by
  by_contra hper
  exact hg (G.main_failure_sparse_polynomial hc hl hq hpc hper).1

end CriticalPercolation.BondGraph
end
end

end OAI
