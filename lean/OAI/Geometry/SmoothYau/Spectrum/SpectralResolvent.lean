import Mathlib
import OAI.Geometry.SmoothYau.Limits.ManifoldSobolevInclusionCoordinate

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def spectralResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) : A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  manifoldSobolevInclusion A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
    A.chart_η A.smooth_η (2 * ((k + 1 : ℕ) : ℝ)) (2 * (k : ℝ)) ∘L A.resolvent B α hα he

omit [T2Space M] in
theorem spectralResolvent_compact (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) : IsCompactOperator (A.spectralResolvent B α hα he) := by
  apply (manifoldSobolevInclusion_compact A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η k ?_).comp_clm
  push_cast
  linarith
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
