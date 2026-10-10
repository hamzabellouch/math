import Mathlib
import OAI.Geometry.SmoothYau.Geometry.PinnedMetricJointGradientPair
import OAI.Geometry.SmoothYau.Smoothness.ChartTensorCoordLocal1
import OAI.Geometry.SmoothYau.Smoothness.PinningTensorSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma pinnedMetric_continuousSmoothFamily (g : SmoothMetric E M)
    {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U)
    (p : M) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn
      (fun t y => metricCoefficients (pinnedMetric g K.val K.property.1 t) p y i j)
      (chartAt E p).target := by
  refine ⟨?_,fun n z hz => ?_⟩
  · intro t y hy
    exact (contDiffOn_metricCoefficient (pinnedMetric g K.val K.property.1 t) p i j).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)
  · exact (continuousAt_partial_iteratedFDeriv _ n
      (pinnedMetric_joint_coefficients g K.val K.property.1 p i j z.1 hz.2)).continuousWithinAt
lemma pinnedMetric_preserves_eigenfunction (g : SmoothMetric E M)
    {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) {lam : ℝ}
    (he : ∀ x, -laplaceBeltrami g u x=lam*u x) (t : ℝ) :
    ∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) u x=lam*u x := by
  intro x
  rw [pinnedMetric_laplacian g K.val K.property.1 K.property.2.1 K.property.2.2.1 hu K.property.2.2.2.1]
  exact he x
lemma pinnedMetric_exterior (g : SmoothMetric E M)
    {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U) (t : ℝ)
    (x : M) (hx : x ∉ U) : (pinnedMetric g K.val K.property.1 t).inner x=g.inner x :=
  pinnedMetric_unchanged g K.val K.property.1 t x (K.property.2.2.2.2 x hx)
end YauCounterexamples
end

end OAI
