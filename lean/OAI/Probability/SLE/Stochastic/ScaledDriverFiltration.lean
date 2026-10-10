import OAI.Probability.SLE.Loewner.RestartDriverScaling

namespace OAI

/-! The natural past of the capacity-scaled Brownian driver is exactly
the original past after the deterministic quadratic time change. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

variable {Ω : Type*} [MeasurableSpace Ω]

def scaledBrownianDriver (c : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (c:ℝ)*B (sourceScaleTime c t) ω

lemma scaledBrownianDriver_measurable (c : ℝ≥0) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    Measurable (scaledBrownianDriver c B t) := measurable_const.mul (hm _)

omit [MeasurableSpace Ω] in
lemma scaledBrownianDriver_continuous (c : ℝ≥0) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    Continuous (fun t => scaledBrownianDriver c B t ω) :=
  continuous_const.mul ((hc ω).comp (continuous_id.div_const (c^2)))

lemma scaledBrownianDriver_brownian {P : Measure Ω} (c : ℝ≥0) (hc : 0 < c)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    IsBrownianReal (scaledBrownianDriver c B) P := by
  change IsBrownianReal (fun t ω => (c:ℝ)*B (t/(c^2)) ω) P
  have h := hB.smul (c := (c^2)⁻¹) (inv_ne_zero (pow_ne_zero 2 hc.ne'))
  simpa only [scaledBrownianDriver,sourceScaleTime,NNReal.coe_inv,NNReal.coe_pow,
    Real.sqrt_inv,Real.sqrt_sq c.coe_nonneg,inv_inv,div_eq_mul_inv,mul_comm] using h

lemma scaledBrownianDriver_filtration (c : ℝ≥0) (hc : 0 < c)
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    (Filtration.natural (scaledBrownianDriver c B)
      (fun s => (scaledBrownianDriver_measurable c B hm s).stronglyMeasurable)) (c^2*t)=
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t := by
  let ℱ := Filtration.natural B (fun s => (hm s).stronglyMeasurable)
  let 𝒢 := Filtration.natural (scaledBrownianDriver c B)
    (fun s => (scaledBrownianDriver_measurable c B hm s).stronglyMeasurable)
  have hc2 : 0 < c^2 := pow_pos hc 2
  apply le_antisymm
  · change (⨆ s ≤ c^2*t,
      MeasurableSpace.comap (scaledBrownianDriver c B s) (borel ℝ)) ≤ ℱ t
    refine iSup₂_le fun s hs => measurable_iff_comap_le.mp ?_
    have hst : sourceScaleTime c s ≤ t := by
      exact (div_le_iff₀ hc2).mpr (by simpa only [mul_comm] using hs)
    have hBm : Measurable[ℱ t] (B (sourceScaleTime c s)) :=
      ((Filtration.stronglyAdapted_natural (fun r => (hm r).stronglyMeasurable)
        (sourceScaleTime c s)).mono (ℱ.mono hst)).measurable
    exact measurable_const.mul hBm
  · change (⨆ s ≤ t, MeasurableSpace.comap (B s) (borel ℝ)) ≤ 𝒢 (c^2*t)
    refine iSup₂_le fun s hs => measurable_iff_comap_le.mp ?_
    have hst : c^2*s ≤ c^2*t := mul_le_mul_of_nonneg_left hs zero_le
    have hYm : Measurable[𝒢 (c^2*t)] (scaledBrownianDriver c B (c^2*s)) :=
      ((Filtration.stronglyAdapted_natural (fun r =>
        (scaledBrownianDriver_measurable c B hm r).stronglyMeasurable)
        (c^2*s)).mono (𝒢.mono hst)).measurable
    have he : B s=(fun ω => (c:ℝ)⁻¹*scaledBrownianDriver c B (c^2*s) ω) := by
      funext ω
      change B s ω=(c:ℝ)⁻¹*((c:ℝ)*B ((c^2*s)/c^2) ω)
      rw [mul_div_cancel_left₀ _ hc2.ne',inv_mul_cancel_left₀ (show (c:ℝ) ≠ 0 by exact_mod_cast hc.ne')]
    rw [he]
    exact measurable_const.mul hYm

lemma scaledBrownianDriver_path_law {P : Measure Ω}
    (c : ℝ≥0) (hc : 0 < c) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous (fun t => B t ω)) :
    P.map (sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hcont))=
      P.map (sourceDriverPath B hcont) :=
  (ScaleTraceLaw.brownian_continuous_path_law B (scaledBrownianDriver c B)
    hB (scaledBrownianDriver_brownian c hc hB) hm (scaledBrownianDriver_measurable c B hm)
    hcont (scaledBrownianDriver_continuous c B hcont)).symm

end SLEExactGauge

end

end OAI
