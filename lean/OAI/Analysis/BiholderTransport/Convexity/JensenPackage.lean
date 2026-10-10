import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.PoleCoordinates

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

abbrev chartOuterEnvelope (v : M → ℝ) (t : ℝ) (a : M) : Model n → ℝ :=
  fun z=>hopfLax t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm z)
abbrev chartCenterEnvelope (g : M → ℝ) (t : ℝ) (a : M) : Model n → ℝ :=
  fun z=>hopfLax (1-t) g ((extChartAt 𝓘(ℝ,Model n) a).symm z)
abbrev chartActualPole (v : M → ℝ) (t : ℝ) (a : M) : Model n → M :=
  fun z=>hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm z)
end WeakMTWTransport

end

end OAI
