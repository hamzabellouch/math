import OAI.Probability.SLE.Loewner.CanonicalRadiusKernel
import OAI.Probability.SLE.OccupationBound

namespace OAI

/-! A jointly measurable canonical kernel for the one-point approach
estimate permits random marked-state substitution at a stopped past. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance approachDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance approachDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

theorem canonical_radius_approach
    (ν : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ν]
    (hB : IsBrownianReal (fun (t : ℝ≥0) (p : C(ℝ≥0, ℝ)) => p t) ν)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ p ∂ν, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p))
    (w : ℂ) (hwH : w ∈ upperHalfPlane) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ)) :
    ν {p | canonicalRadiusLevel κ ((v : ℝ), w, p) < ∞} ≤
      ENNReal.ofReal (uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        (Real.sin (Complex.arg w)) ^ greenExponent κ) := by
  have he : ν {p | canonicalRadiusLevel κ ((v : ℝ), w, p) < ∞} =
      ν {p | radiusLevelTime (Φ p) (Gc p) w v < ∞} := by
    apply measure_congr
    filter_upwards [hw] with p hp
    rw [canonicalRadiusLevel_eq κ p hp _ v.coe_nonneg w]
  rw [he]
  calc
    _ = ENNReal.ofReal (ν {p | radiusLevelTime (Φ p) (Gc p) w v < ∞}).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (radius_approach hB κ hκ hκ8
      (fun p t => Φ p t) Gc Fc hw w hwH v hv)

end SLEExactGauge

end

end OAI
