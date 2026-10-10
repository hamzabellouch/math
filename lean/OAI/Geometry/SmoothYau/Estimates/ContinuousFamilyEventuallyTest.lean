import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ChartTensorCoordLocal1

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
namespace YauCounterexamples
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma continuousFamily_eventually_test (q : P → SmoothMetric E M)
    (hq : ∀ r i j, ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (q a) r y i j) (chartAt E r).target)
    (a₀ : P) (t : CoordinateTest E M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in 𝓝 a₀, ∀ y ∈ t.compactSet,
      ‖iteratedFDeriv ℝ t.order (fun z => metricCoefficients (q a) t.center z t.row t.column -
        metricCoefficients (q a₀) t.center z t.row t.column) y‖ < ε := by
  apply t.isCompact.eventually_forall_of_forall_eventually
  intro y hy
  have hf := (hq t.center t.row t.column).sub (ContinuousSmoothFamilyOn.const
    (fun y => metricCoefficients (q a₀) t.center y t.row t.column)
    (fun y hy => (hq t.center t.row t.column).smooth a₀ y hy))
  have hc := (hf.jets t.order).continuousAt (x := (a₀,y))
    ((isOpen_univ.prod (chartAt E t.center).open_target).mem_nhds ⟨mem_univ _,t.inTarget hy⟩)
  apply hc.norm.eventually (gt_mem_nhds ?_)
  simp only [sub_self,iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
  exact hε
lemma continuousFamily_eventually_neighborhood (q : P → SmoothMetric E M)
    (hq : ∀ r i j, ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (q a) r y i j) (chartAt E r).target)
    (a₀ : P) {N : Set (SmoothMetric E M)} (hN : IsSmoothNeighborhood (q a₀) N) :
    ∀ᶠ a in 𝓝 a₀, q a ∈ N := by
  obtain ⟨tests,ε,hε,hN⟩ := hN
  have hh : ∀ᶠ a in 𝓝 a₀, ∀ t ∈ tests, ∀ y ∈ t.compactSet,
      ‖iteratedFDeriv ℝ t.order (fun z => metricCoefficients (q a) t.center z t.row t.column -
        metricCoefficients (q a₀) t.center z t.row t.column) y‖ < ε := by
    apply (Filter.eventually_all_finite tests.finite_toSet).mpr
    intro t ht
    exact continuousFamily_eventually_test q hq a₀ t hε
  exact hh.mono (fun a ha => hN (q a) ha)
end YauCounterexamples
end

end OAI
