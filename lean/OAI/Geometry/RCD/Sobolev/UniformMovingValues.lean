import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

namespace OAI

/-! # Evaluating local uniform convergence along converging points -/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem uniform_subtype_moving_values {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {S : Set X} {f : ℕ → X → Y} {g : X → Y} {u : ℕ → X} {x : X}
    (hf : TendstoUniformly (fun k (y : S) => f k y) (fun y => g y) atTop)
    (hu : Tendsto u atTop (𝓝 x)) (hg : ContinuousAt g x)
    (hS : ∀ᶠ k in atTop, u k ∈ S) :
    Tendsto (fun k => f k (u k)) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := (hg.tendsto.comp hu).eventually (Metric.ball_mem_nhds (g x) (by linarith : 0 < ε/2))
  filter_upwards [hS,(Metric.tendstoUniformly_iff.mp hf) (ε/2) (by linarith),hh] with k hk hf' hu'
  have hv : dist (f k (u k)) (g (u k)) < ε/2 := by
    simpa only [dist_comm] using hf' ⟨u k,hk⟩
  have hw : dist (g (u k)) (g x) < ε/2 := hu'
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end RegularPointCoordinates

end OAI
