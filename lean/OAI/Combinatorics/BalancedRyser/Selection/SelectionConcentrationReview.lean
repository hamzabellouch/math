import OAI.Combinatorics.BalancedRyser.Selection.SelectionConcentrationUniform
import OAI.Combinatorics.BalancedRyser.Selection.SelectionSuccessUniform

namespace OAI

open Filter
open scoped Topology
namespace Balanced.Selection.Process
universe u v
example (p : Parameters) (hp : p.Admissible) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop, UniformConcentrationEstimate.{u,v} p ε q :=
  exists_uniformConcentratedPath_estimate p hp

end Balanced.Selection.Process

end OAI
