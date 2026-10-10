import OAI.Probability.SLE.Gauge.GaugeCrosscutDischarge
import OAI.Probability.SLE.Geometry.ActualGeometricTubeSupport

namespace OAI

/-! The explicit exact Hausdorff gauge theorem for ordinary chordal SLE. -/
noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem ordinary_explicit_mainConclusion_unconditional
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8) (γ : Ω → ℝ≥0 → ℂ)
    (hSLE : IsOrdinaryChordalSLE κ γ P) :
    MainConclusion P (explicitGauge κ) γ :=
  ordinary_explicit_mainConclusion_of_support P κ hκ hκ8 γ hSLE
    (ordinary_geometricTubeSupport P κ hκ γ hSLE)

end SLEExactGauge

end

end OAI
