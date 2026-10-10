import OAI.Probability.SLE.Geometry.NormalizedRawRestart

namespace OAI

/-! Every measurable full-law certificate is retained by the randomly
normalized fresh driver, on the original probability space. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance normalizedGoodMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance normalizedGoodBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma normalized_restart_mem_full_driver_set
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (a : Ω → ℝ≥0) (haM : Measurable[hτ.measurableSpace] a) (ha : ∀ ω, 0 < a ω)
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E) :
    ∀ᵐ ω ∂P, scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω) ∈ E := by
  let Y : Ω → C(ℝ≥0,ℝ) := fun ω =>
    scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω)
  have hY : Measurable Y := measurable_scaleDriverPath.comp
    ((haM.mono hτ.measurableSpace_le le_rfl).inv.prodMk
      (sourceRestartDriverPath_measurable B hm hc τ hτ))
  have hlaw : P.map Y=P.map (sourceDriverPath B hc) := by
    simpa only [Measure.restrict_univ,measure_univ,one_smul] using
      source_restart_random_scale_driver_law B hB hm hc τ hτ
        (fun ω => (a ω)⁻¹) haM.inv (fun ω => inv_pos.mpr (ha ω))
        univ MeasurableSet.univ
  apply (ae_map_iff hY.aemeasurable hE).mp
  rwa [hlaw]

end SLEExactGauge

end

end OAI
