import OAI.Geometry.EinsteinFour.FrameRegularity
import OAI.Geometry.EinsteinFour.JacobiVolume

namespace OAI

/-! Application of the proved radial determinant estimate to the actual
frame-curvature fields. The geometric premises retain the ordinary Jacobi
equation and polar integration formula; no radial deficit is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

local instance : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace

/-- Once the two time-zero energies have been obtained by spherical
integration, the classical parallel-frame/Jacobi/polar construction gives
the manuscript's upper-volume deficit. -/
theorem volume_ratio_upper_of_frame_flow
    (g : SmoothMetric M) [CompactSpace (FrameBundle g)]
    {μ : Measure (FrameBundle g)} [IsProbabilityMeasure μ]
    (φ : FrameFlow g μ)
    (hC : Continuous (frameCurvatureField g))
    (hH : Continuous (frameCurvatureDerivative g))
    (hpoint : ∀ t e, HasDerivAt
      (fun r => frameCurvatureField g (φ.map r e))
      (frameCurvatureDerivative g (φ.map t e)) t)
    {s : ℝ}
    (hCmean : (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ) = (3 / 2) * s)
    (hHmean : (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) ≤ (9 / 4) * s)
    (d : (u : ℝ) → FrameBundle g → Jacobi.RegularJacobi (Real.pi * u))
    (hR : ∀ u e r, (d u e).R r = 1 + frameCurvatureField g (φ.map r e))
    (hpos : ∀ u e r, ((d u e).R r).PosSemidef)
    (htrace : ∀ u e r, ((d u e).R r).trace = 3)
    (hD : ∀ u, 0 < u → u < 1 → Integrable (fun e => (d u e).truncatedDensity) μ)
    (hD0 : IntervalIntegrable (fun u => ∫ e, (d u e).truncatedDensity ∂μ)
      volume 0 (5 / 8))
    (hD1 : IntervalIntegrable (fun u => ∫ e, (d u e).truncatedDensity ∂μ)
      volume (5 / 8) 1)
    (hpolar : volumeRatio g ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), ∫ e, (d u e).truncatedDensity ∂μ) +
        ∫ u in (5 / 8 : ℝ)..1, ∫ e, (d u e).truncatedDensity ∂μ)) :
    volumeRatio g ≤ 1 - (3 / 40) * s := by
  have hs : 0 ≤ s := by
    have hnonneg : 0 ≤ ∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    rw [hCmean] at hnonneg
    linarith
  have hLip (u : ℝ) (_hu : 0 < u) (_hu1 : u < 1) (e : FrameBundle g) :
      ∃ L : ℝ, 0 ≤ L ∧ ∀ a b,
        ‖Averages.sineWeight a • Jacobi.radialCurvature (d u e).R (Real.pi * u) a -
          Averages.sineWeight b • Jacobi.radialCurvature (d u e).R (Real.pi * u) b‖ ≤
            L * |a - b| := by
    obtain ⟨L, hL, hbound⟩ := frameWeighted_lipschitz φ hC hH hpoint (Real.pi * u) e
    refine ⟨L, hL, ?_⟩
    intro a b
    simpa only [Jacobi.radialCurvature, hR, add_sub_cancel_left, mul_comm]
      using hbound a b
  exact Jacobi.volume_ratio_upper_of_jacobi d hs
    (curvatureCurve_hasDerivAt φ hC hH hpoint)
    (curvatureCurve_energy φ hC hCmean)
    (curvatureDerivativeCurve_energy φ hH hHmean)
    hR hpos htrace hLip hD hD0 hD1 hpolar

end

end PositiveEinsteinFour.Geometry

end OAI
