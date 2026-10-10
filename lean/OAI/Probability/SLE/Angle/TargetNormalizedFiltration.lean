import OAI.Probability.SLE.Angle.TargetBrownianNormalization

namespace OAI

/-! The exact time change of the natural Brownian past for the
source-prescribed normalized driver. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def normalizedFiltration (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0) : Filtration ℝ≥0 mΩ :=
  Filtration.natural (fun t ω => normalizedDriver κ B hc h0 ω t)
    (fun t => ((continuous_eval_const t).measurable.comp
      (normalizedDriver_measurable κ B hm hc h0)).stronglyMeasurable)

theorem normalizedFiltration_scaled (κ : ℝ) (hκ : 0<κ)
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0) (t : ℝ≥0) :
    normalizedFiltration κ B hm hc h0 (κ.toNNReal*t)=
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t := by
  let ℱ := Filtration.natural B (fun s => (hm s).stronglyMeasurable)
  let 𝒢 := normalizedFiltration κ B hm hc h0
  have hp : 0<κ.toNNReal := Real.toNNReal_pos.mpr hκ
  apply le_antisymm
  · change (⨆ s ≤ κ.toNNReal*t,
      MeasurableSpace.comap (fun ω => normalizedDriver κ B hc h0 ω s) (borel ℝ)) ≤ ℱ t
    refine iSup₂_le fun s hs => measurable_iff_comap_le.mp ?_
    have hst : s/κ.toNNReal ≤ t := (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hs)
    have hBm : Measurable[ℱ t] (B (s/κ.toNNReal)) :=
      ((Filtration.stronglyAdapted_natural (fun r => (hm r).stronglyMeasurable)
        (s/κ.toNNReal)).mono (ℱ.mono hst)).measurable
    exact measurable_const.mul hBm
  · change (⨆ s ≤ t, MeasurableSpace.comap (B s) (borel ℝ)) ≤ 𝒢 (κ.toNNReal*t)
    refine iSup₂_le fun s hs => measurable_iff_comap_le.mp ?_
    have hst : κ.toNNReal*s ≤ κ.toNNReal*t := mul_le_mul_of_nonneg_left hs zero_le
    have hYm : Measurable[𝒢 (κ.toNNReal*t)]
        (fun ω => normalizedDriver κ B hc h0 ω (κ.toNNReal*s)) :=
      ((Filtration.stronglyAdapted_natural (fun r =>
        ((continuous_eval_const r).measurable.comp
          (normalizedDriver_measurable κ B hm hc h0)).stronglyMeasurable)
        (κ.toNNReal*s)).mono (𝒢.mono hst)).measurable
    have he : B s=(fun ω => (Real.sqrt κ)⁻¹*normalizedDriver κ B hc h0 ω (κ.toNNReal*s)) := by
      funext ω
      change B s ω=(Real.sqrt κ)⁻¹*(Real.sqrt κ*B ((κ.toNNReal*s)/κ.toNNReal) ω)
      rw [mul_div_cancel_left₀ _ hp.ne',inv_mul_cancel_left₀ (Real.sqrt_pos.mpr hκ).ne']
    rw [he]
    exact measurable_const.mul hYm

theorem normalizedFiltration_at (κ : ℝ) (hκ : 0<κ)
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0) (t : ℝ≥0) :
    normalizedFiltration κ B hm hc h0 t=
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)) (t/κ.toNNReal) := by
  have h := normalizedFiltration_scaled κ hκ B hm hc h0 (t/κ.toNNReal)
  simpa only [mul_div_cancel₀ _ (Real.toNNReal_pos.mpr hκ).ne'] using h

end SLEExactGauge.Target

end

end OAI
