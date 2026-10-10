import OAI.Probability.SLE.Geometry.ActualExplicitTransfer
import OAI.Probability.SLE.Geometry.ActualWienerSupport

namespace OAI

/-! The explicit exact-gauge theorem using planar Wiener support
derived from the Brownian law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance explicitDischargeMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance explicitDischargeBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem ordinary_explicit_mainConclusion_of_remaining_inputs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (htrace : PublishedTraceGeneration (ordinaryRegularDriverLaw hSLE) κ (fun t p => p t))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw) :
    MainConclusion P (explicitGauge κ) γ :=
  ordinary_explicit_mainConclusion_of_published_inputs P κ hκ hκ8 γ hSLE
    htrace hcompact hboundary hsupport hplanar hstraight hexit actual_planarWienerUnitSupport

end SLEExactGauge

end

end OAI
