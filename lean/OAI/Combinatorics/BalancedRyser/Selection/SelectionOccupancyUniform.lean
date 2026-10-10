import OAI.Combinatorics.BalancedRyser.Selection.SelectionOccupancyFinal
import OAI.Combinatorics.BalancedRyser.Selection.SelectionSuccessUniform

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Balanced.Selection.Process
universe u v w

theorem exists_uniformOccupancyEstimate (p : Parameters) (hp : p.Admissible) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop, UniformOccupancyEstimate.{u,v,w} p ε q := by
  refine ⟨fun q => 2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q),
    source_occupancy_error_tendsto p hp, ?_⟩
  exact eventually_outputLaw_occupancy_bound.{u,v,w} p hp

theorem selectionStatement_of_uniform_concentration
    (hconcentration : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformConcentrationEstimate.{u,v} p ε q) :
    SelectionStatement.{u,v,w} := by
  exact selectionStatement_of_uniform_concentration_occupancy hconcentration
    exists_uniformOccupancyEstimate

end Balanced.Selection.Process

end

end OAI
