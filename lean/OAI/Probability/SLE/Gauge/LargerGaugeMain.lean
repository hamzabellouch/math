import OAI.Probability.SLE.LowerPositivity
import OAI.Probability.SLE.Gauge.ExactGaugeComparison
import OAI.Probability.SLE.Gauge.GaugeCompletion

namespace OAI

/-! The larger-gauge corollary in the introduction of the explicit-gauge paper. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- On one event, every positive-time compact SLE segment has non-sigma-finite
Hausdorff measure for Schramm's proposed exponent-one log-log gauge, by
comparison with the explicit gauge's positive Hausdorff measure. -/
theorem larger_gauge_not_sigmaFinite_on_all_segments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h g : ℝ → ℝ) (hh : IsGauge h) (hg : IsGauge g)
    (hf : HasSmallRadiusFormula h (hFormula κ))
    (gf : HasSmallRadiusFormula g (gFormula κ)) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      ¬ SigmaFinite ((hausdorffGauge g).restrict (segment (γ ω) s t)) := by
  have hlo := sourceLowerMain_proved Ω inferInstance P inferInstance
    κ hκ hκ8 γ hSLE h hh hf
  filter_upwards [hlo] with ω hω s t hs hst
  exact larger_logLog_gauge_not_sigmaFinite hκ hh hg hf gf (hω s t hs hst)

/-- The same simultaneous event gives infinite total larger-gauge measure. -/
theorem larger_gauge_infinite_on_all_segments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h g : ℝ → ℝ) (hh : IsGauge h) (hg : IsGauge g)
    (hf : HasSmallRadiusFormula h (hFormula κ))
    (gf : HasSmallRadiusFormula g (gFormula κ)) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      hausdorffGauge g (segment (γ ω) s t) = ∞ := by
  have hlo := sourceLowerMain_proved Ω inferInstance P inferInstance
    κ hκ hκ8 γ hSLE h hh hf
  filter_upwards [hlo] with ω hω s t hs hst
  exact hausdorffGauge_larger_eq_top_of_positive hh hg
    (gauge_ratio_tendsto_zero hκ hf gf) (hω s t hs hst)

/-- The paper's larger-gauge corollary with deterministic gauges constructed
in Lean, so no existence or completion hypothesis remains. -/
theorem schramm_gauge_not_sigmaFinite_on_all_segments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      ¬ SigmaFinite ((hausdorffGauge (schrammGauge κ)).restrict
        (segment (γ ω) s t)) :=
  larger_gauge_not_sigmaFinite_on_all_segments P κ hκ hκ8 γ hSLE
    (explicitGauge κ) (schrammGauge κ)
    (explicitGauge_isGauge hκ) (schrammGauge_isGauge hκ)
    (explicitGauge_small_formula κ) (schrammGauge_small_formula κ)

/-- Infinite total measure for the concrete exponent-one log-log gauge. -/
theorem schramm_gauge_infinite_on_all_segments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      hausdorffGauge (schrammGauge κ) (segment (γ ω) s t) = ∞ :=
  larger_gauge_infinite_on_all_segments P κ hκ hκ8 γ hSLE
    (explicitGauge κ) (schrammGauge κ)
    (explicitGauge_isGauge hκ) (schrammGauge_isGauge hκ)
    (explicitGauge_small_formula κ) (schrammGauge_small_formula κ)

end SLEExactGauge

end

end OAI
