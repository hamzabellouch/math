import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.TwoPoint
import OAI.Probability.CriticalPercolation.Modular.LightClusterNumber
import OAI.Probability.CriticalPercolation.GraphGeometry.EncounterGeometry
import OAI.Probability.CriticalPercolation.Modular.LightTwoPointDecay
import OAI.Probability.CriticalPercolation.Modular.MainInfiniteLightBoundary

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infinitelyManyLightClusters.infinite {ω : Set E}
    (h : G.infinitelyManyLightClusters ω) : G.infinitelyManyInfiniteClusters ω := by
  intro S
  obtain ⟨v,hv,hs⟩ := h S
  exact ⟨v,hv.1,hs⟩

theorem main_all_light_or_sparse_boundary [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (o : V)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    (¬G.CombinatoriallyUnimodular ∧
      (∀ᵐ ω ∂G.law G.criticalProbability, G.infinitelyManyLightClusters ω ∧
        ∀ v, G.modularMass o (G.cluster ω v)<∞) ∧
      (∀ ε : ℝ, 0<ε → ∃ R : ℕ, ∀ x y, y∉G.vertexBall x R →
        CriticalPercolation.Sharpness.twoPoint G G.criticalProbability x y<ε) ∧
      (∀ k : ℕ, ∃ J : Set E, J.Finite ∧
        0<G.law G.criticalProbability (G.encounterEvent J o k))) ∨
    (G.SubexponentialGrowth ∧ ∃ d : ℕ, 2≤d ∧
      ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  rcases G.main_infinite_light_or_sparse_boundary hc hl hq hpc o hper with
    ⟨hu,hlight,_⟩|hpoly
  · have hp : 0<G.criticalProbability := by
      by_contra hn
      have he : G.criticalProbability=0 := le_antisymm (le_of_not_gt hn) bot_le
      exact hper (by rw [he,G.law_zero_percolates])
    refine Or.inl ⟨hu,hlight.and (G.nonunimodular_critical_mass_finite_ae hc hl hq hpc hu o),
      G.nonunimodular_critical_twoPoint_decay hc hl hq hpc hu,?_⟩
    intro k
    exact G.exists_positive_encounter hc G.criticalProbability hp o k
      (hlight.mono (fun _ h => h.infinite G))
  · exact Or.inr hpoly

end CriticalPercolation.BondGraph
end
end

end OAI
