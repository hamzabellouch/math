import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

namespace OAI

/-! # Polarized energy convergence from sharp diagonal upper bounds

The lower bound for each fixed linear combination forces the mixed entry
of the quadratic forms to converge. Only the combinations +1 and -1 are
needed once both diagonal upper bounds are sharp.
-/

open Filter
open scoped Topology
namespace RegularPointCoordinates

theorem cross_tendsto_of_quadratic_lower {E F C : ℕ → ℝ} {a b c : ℝ}
    (hE : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, E k≤a+δ)
    (hF : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, F k≤b+δ)
    (hlower : ∀ t δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      a+2*t*c+t^2*b-δ≤E k+2*t*C k+t^2*F k) :
    Tendsto C atTop (𝓝 c) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0<ε/4 := by positivity
  filter_upwards [hE (ε/4) hδ,hF (ε/4) hδ,
    hlower 1 (ε/4) hδ,hlower (-1) (ε/4) hδ] with k he hf hp hm
  rw [Real.dist_eq,abs_lt]
  constructor <;> nlinarith

end RegularPointCoordinates

end OAI
