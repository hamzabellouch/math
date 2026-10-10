import OAI.Probability.SLE.Gauge.GaugeTraceDischarge
import OAI.Probability.SLE.Geometry.HalfPlaneCompactnessFromGrowth
import OAI.Probability.SLE.Geometry.HalfPlaneCompactnessBloch
import OAI.Probability.SLE.Stochastic.PlanarDiskOpenness

namespace OAI

/-! The explicit gauge needs no independent normal-family input once
the disk growth estimate is available. -/
noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem ordinary_explicit_mainConclusion_of_boundary_support_crosscut_exit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw) :
    MainConclusion P (explicitGauge κ) γ :=
  ordinary_explicit_mainConclusion_of_conformal_inputs P κ hκ hκ8 γ hSLE
    actual_halfPlaneUnivalentCompactness hboundary hsupport actual_planarDiskOpenness hstraight hexit

theorem ordinary_explicit_mainConclusion_of_geometric_inputs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw) :
    MainConclusion P (explicitGauge κ) γ :=
  ordinary_explicit_mainConclusion_of_conformal_inputs P κ hκ hκ8 γ hSLE
    actual_halfPlaneUnivalentCompactness hboundary hsupport hplanar hstraight hexit

theorem ordinary_explicit_mainConclusion_of_growth_and_geometric_inputs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw) :
    MainConclusion P (explicitGauge κ) γ :=
  ordinary_explicit_mainConclusion_of_conformal_inputs P κ hκ hκ8 γ hSLE
    (halfPlaneUnivalentCompactness_of_diskGrowth hgrowth) hboundary hsupport hplanar hstraight hexit

end SLEExactGauge

end

end OAI
