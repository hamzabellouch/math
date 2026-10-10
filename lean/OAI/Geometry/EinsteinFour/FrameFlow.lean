import OAI.Geometry.EinsteinFour.FrameAverages
import OAI.Geometry.EinsteinFour.ContinuousFieldDerivative

namespace OAI

/-! The frame-flow action on the actual normal-curvature fields. The
measure-preserving continuous action is the precise part of Brin--Karcher,
Section 1, used here; no ergodicity or curvature-energy bound is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace

structure FrameFlow (g : SmoothMetric M) (μ : Measure (FrameBundle g)) where
  map : ℝ → FrameBundle g ≃ᵐ FrameBundle g
  continuous : Continuous (fun p : ℝ × FrameBundle g => map p.1 p.2)
  preserves : ∀ t, MeasurePreserving (map t) μ μ

theorem FrameFlow.continuous_slice {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (t : ℝ) : Continuous (φ.map t) :=
  φ.continuous.comp (continuous_const.prodMk continuous_id)

def curvatureCurve {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hC : Continuous (frameCurvatureField g))
    (t : ℝ) : C(FrameBundle g, Mat3) :=
  ⟨fun e => frameCurvatureField g (φ.map t e), hC.comp (φ.continuous_slice t)⟩

def curvatureDerivativeCurve {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hH : Continuous (frameCurvatureDerivative g))
    (t : ℝ) : C(FrameBundle g, Mat3) :=
  ⟨fun e => frameCurvatureDerivative g (φ.map t e), hH.comp (φ.continuous_slice t)⟩

/-- The ordinary derivative along each parallel frame implies the derivative
of the full continuous field used in the radial averaging theorem. -/
theorem curvatureCurve_hasDerivAt {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] (φ : FrameFlow g μ)
    (hC : Continuous (frameCurvatureField g))
    (hH : Continuous (frameCurvatureDerivative g))
    (hpoint : ∀ t e, HasDerivAt
      (fun s => frameCurvatureField g (φ.map s e))
      (frameCurvatureDerivative g (φ.map t e)) t) (t : ℝ) :
    HasDerivAt (curvatureCurve φ hC) (curvatureDerivativeCurve φ hH t) t := by
  apply Averages.continuousField_hasDerivAt_of_joint
  · exact hH.comp φ.continuous
  · exact hpoint

theorem curvatureCurve_stationary {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hC : Continuous (frameCurvatureField g)) (t : ℝ) :
    (∫ e, ‖curvatureCurve φ hC t e‖ ^ 2 ∂μ) =
      ∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ := by
  exact (φ.preserves t).integral_comp' (fun e => ‖frameCurvatureField g e‖ ^ 2)

theorem curvatureDerivativeCurve_stationary {g : SmoothMetric M}
    {μ : Measure (FrameBundle g)} (φ : FrameFlow g μ)
    (hH : Continuous (frameCurvatureDerivative g)) (t : ℝ) :
    (∫ e, ‖curvatureDerivativeCurve φ hH t e‖ ^ 2 ∂μ) =
      ∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ := by
  exact (φ.preserves t).integral_comp' (fun e => ‖frameCurvatureDerivative g e‖ ^ 2)

theorem curvatureCurve_energy {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hC : Continuous (frameCurvatureField g)) {s : ℝ}
    (hs : (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ) = (3 / 2) * s) :
    ∀ t, (∫ e, ‖curvatureCurve φ hC t e‖ ^ 2 ∂μ) = (3 / 2) * s := by
  intro t
  rw [curvatureCurve_stationary, hs]

theorem curvatureDerivativeCurve_energy {g : SmoothMetric M}
    {μ : Measure (FrameBundle g)} (φ : FrameFlow g μ)
    (hH : Continuous (frameCurvatureDerivative g)) {s : ℝ}
    (hs : (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) ≤ (9 / 4) * s) :
    ∀ t, (∫ e, ‖curvatureDerivativeCurve φ hH t e‖ ^ 2 ∂μ) ≤
      (3 / 2) * ((3 / 2) * s) := by
  intro t
  rw [curvatureDerivativeCurve_stationary]
  linarith

end

end PositiveEinsteinFour.Geometry

end OAI
