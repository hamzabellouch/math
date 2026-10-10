import OAI.Probability.SLE.Loewner.CanonicalTraceDischarge
import OAI.Probability.SLE.Gauge.PrescribedPublishedMain
import OAI.Probability.SLE.Geometry.ExplicitInputDischarge

namespace OAI

/-! Exact gauge theorems using canonical trace generation and explicit
conformal hypotheses. -/
noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance gaugeTraceRealMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance gaugeTraceRealBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem RegularSLEPresentation.canonical_driver_trace_generation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    PublishedTraceGeneration
      ((P.comap (Subtype.val : a.samples → Ω)).map (sourceDriverPath a.B a.continuous_B))
      κ (fun t p => p t) :=
  canonical_driver_trace_generation_of_witness κ hκ hκ8 a.B a.brownian
    a.measurable_B a.continuous_B a.zero_B (fun ω => γ ω) a.G a.F a.witness

theorem ordinary_prescribed_mainConclusion_of_univalent_growth
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hgrowth : PublishedDiskUnivalentGrowth)
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    MainConclusion P (Target.gauge κ W) γ :=
  ordinary_prescribed_mainConclusion_of_published_inputs P κ hκ hκ8 γ hSLE hgrowth
    ((ordinaryRegularPresentation hSLE).canonical_driver_trace_generation hκ hκ8) W hW

theorem ordinary_explicit_mainConclusion_of_conformal_inputs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw) :
    MainConclusion P (explicitGauge κ) γ :=
  ordinary_explicit_mainConclusion_of_remaining_inputs P κ hκ hκ8 γ hSLE
    ((ordinaryRegularPresentation hSLE).canonical_driver_trace_generation hκ hκ8)
    hcompact hboundary hsupport hplanar hstraight hexit

end SLEExactGauge

end

end OAI
