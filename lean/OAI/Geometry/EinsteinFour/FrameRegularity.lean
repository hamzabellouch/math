import OAI.Geometry.EinsteinFour.FrameFlow
import OAI.Geometry.EinsteinFour.WeightedCurve

namespace OAI

/-! Boundedness on the compact frame space supplies the weighted Lipschitz
condition required by the proved discrete-to-continuous radial comparison. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace

theorem frameWeighted_lipschitz {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] (φ : FrameFlow g μ)
    (hC : Continuous (frameCurvatureField g))
    (hH : Continuous (frameCurvatureDerivative g))
    (hpoint : ∀ t e, HasDerivAt
      (fun r => frameCurvatureField g (φ.map r e))
      (frameCurvatureDerivative g (φ.map t e)) t)
    (t : ℝ) (e : FrameBundle g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a b,
      ‖Averages.sineWeight a • frameCurvatureField g (φ.map (t * a) e) -
        Averages.sineWeight b • frameCurvatureField g (φ.map (t * b) e)‖ ≤
          L * |a - b| := by
  let : NormedAddCommGroup C(FrameBundle g, Mat3) := ContinuousMap.instNormedAddCommGroup
  let : NormedSpace ℝ C(FrameBundle g, Mat3) := ContinuousMap.normedSpace
  let C : C(FrameBundle g, Mat3) := ⟨_, hC⟩
  let H : C(FrameBundle g, Mat3) := ⟨_, hH⟩
  refine ⟨2 * Real.pi * ‖C‖ + 2 * ‖H‖ * |t|, by positivity, ?_⟩
  intro a b
  exact Averages.sineWeighted_rescale_lipschitz
    (fun r => hpoint r e)
    (fun r => C.norm_coe_le_norm (φ.map r e))
    (fun r => H.norm_coe_le_norm (φ.map r e)) t a b

end

end PositiveEinsteinFour.Geometry

end OAI
