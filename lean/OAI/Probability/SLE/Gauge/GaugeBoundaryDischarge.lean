import OAI.Probability.SLE.Gauge.GaugeConformalReduction
import OAI.Probability.SLE.Geometry.ActualFiniteBoundaryExtension

namespace OAI

/-! The exact explicit-gauge theorem using continuous finite boundary extensions. -/
noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem ordinary_explicit_mainConclusion_of_support_crosscut_exit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw) :
    MainConclusion P (explicitGauge κ) γ :=
  ordinary_explicit_mainConclusion_of_boundary_support_crosscut_exit P κ hκ hκ8 γ hSLE
    actual_finiteLoewnerBoundaryExtension hsupport hstraight hexit

end SLEExactGauge

end

end OAI
