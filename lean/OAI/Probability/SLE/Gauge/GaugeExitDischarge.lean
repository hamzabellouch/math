import OAI.Probability.SLE.Gauge.GaugeBoundaryDischarge
import OAI.Probability.SLE.Geometry.ActualConformalExitLaw

namespace OAI

/-! The exact explicit-gauge theorem using conformal Brownian exit laws. -/
noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem ordinary_explicit_mainConclusion_of_support_crosscut
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hstraight : PublishedHalfPlaneCrosscutStraightening) :
    MainConclusion P (explicitGauge κ) γ :=
  ordinary_explicit_mainConclusion_of_support_crosscut_exit P κ hκ hκ8 γ hSLE
    hsupport hstraight actual_halfPlaneConformalExitLaw

end SLEExactGauge

end

end OAI
