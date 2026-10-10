import OAI.Geometry.RCD.Heat.GaussianHeatInput
import OAI.Geometry.RCD.Heat.AveragedHeatSource

namespace OAI

/-!
# Local finite-difference consequence of the published heat gradient bound

Jiang--Li--Zhang (2016), Corollary 1.2, equation (1.4), bounds the
minimal weak gradient of the kernel by a Gaussian. Local Sobolev-to-Lipschitz,
Bishop--Gromov and kernel continuity give this finite-difference consequence
when the displacement is at most the heat length. The Gaussian constant is
not required to be sharp, and only times at most one are used. The bound is
stated at every source pole, including poles in the singular mass support.
-/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The localized Gaussian gradient estimate, integrated along a short
path, in the only finite-difference form used by the application. -/
def HasGaussianHeatDifferenceBounds (μ : Measure X) (ker : ℝ → X → X → ℝ) : Prop :=
  ∃ C D B : ℝ, 0 < C ∧ 0 < D ∧ 0 ≤ B ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x y z : X, dist x y ≤ Real.sqrt t →
      |ker t x z - ker t y z| ≤
        (C / (Real.sqrt t * μ.real (ball z (Real.sqrt t)))) * dist x y *
          Real.exp (-(dist x z) ^ 2 / (D * t) + B * t)

end RegularPointCoordinates

end

end OAI
