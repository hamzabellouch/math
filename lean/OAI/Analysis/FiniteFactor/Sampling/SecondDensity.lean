import OAI.Analysis.FiniteFactor.Sampling.AveragedTransport
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

def samplingSecondWeight (h α s t : ℝ) : ℝ :=
  samplingWeight false h α (Int.fract (s-t)) t

def samplingSecondDensity (h α s : ℝ) : ℝ :=
  ∫ t, samplingSecondWeight h α s t ∂unitIntervalMeasure

theorem samplingSecondWeight_measurable (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => samplingSecondWeight h α p.1 p.2) :=
  (samplingWeight_measurable false h α).comp
    ((sourceFract_measurable.comp (measurable_fst.sub measurable_snd)).prodMk measurable_snd)

theorem samplingSecondWeight_integrable (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    Integrable (samplingSecondWeight h α s) unitIntervalMeasure := by
  have hm : Measurable (samplingSecondWeight h α s) :=
    (samplingSecondWeight_measurable h α).comp (measurable_const.prodMk measurable_id)
  exact (integrable_const (max 1 (1/(h*α)))).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs]
      change |samplingWeight false h α (Int.fract (s-t)) t| ≤ _
      rw [abs_of_nonneg (samplingWeight_bounds false h α (Int.fract (s-t)) t hh hα).1]
      exact (samplingWeight_bounds false h α _ t hh hα).2))

theorem samplingSecondDensity_lintegral (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    ENNReal.ofReal (samplingSecondDensity h α s) =
      ∫⁻ t, ENNReal.ofReal (samplingSecondWeight h α s t) ∂unitIntervalMeasure :=
  ofReal_integral_eq_lintegral_ofReal (samplingSecondWeight_integrable h α s hh hα)
    (Eventually.of_forall (fun t => (samplingWeight_bounds false h α _ t hh hα).1))

theorem samplingSecondDensity_measurable (h α : ℝ) : Measurable (samplingSecondDensity h α) :=
  (samplingSecondWeight_measurable h α).stronglyMeasurable.integral_prod_right.measurable

theorem samplingSecondDensity_nonneg (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    0 ≤ samplingSecondDensity h α s :=
  integral_nonneg (fun t => (samplingWeight_bounds false h α _ t hh hα).1)

theorem sampling_fract_inverse (z t : ℝ) (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    Int.fract (Int.fract (z+t)-t) = z := by
  have he : Int.fract (z+t)-t = z-(Int.floor (z+t) : ℝ) := by rw [Int.fract]; ring
  rw [he,Int.fract_sub_intCast,Int.fract_eq_self.mpr hz]

/-- Haar substitution identifies the actual second-oriented integral with
the weighted endpoint law; no marginal-density hypothesis is assumed. -/
theorem samplingSecondDensity_test (h α : ℝ) (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, ENNReal.ofReal (samplingSecondDensity h α s)*F s ∂unitIntervalMeasure) =
      ∫⁻ z, ∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t)
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
  have hwm := samplingSecondWeight_measurable h α
  calc
    _ = ∫⁻ s, ∫⁻ t, ENNReal.ofReal (samplingSecondWeight h α s t)*F s
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply lintegral_congr
      intro s
      have hmd : Measurable (fun t => ENNReal.ofReal (samplingSecondWeight h α s t)) :=
        (hwm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
      rw [samplingSecondDensity_lintegral h α s hh hα,lintegral_mul_const _ hmd]
    _ = ∫⁻ t, ∫⁻ s, ENNReal.ofReal (samplingSecondWeight h α s t)*F s
        ∂unitIntervalMeasure ∂unitIntervalMeasure :=
      lintegral_lintegral_swap (hwm.ennreal_ofReal.mul (hF.comp measurable_fst)).aemeasurable
    _ = ∫⁻ t, ∫⁻ z, ENNReal.ofReal (samplingWeight false h α z t)*F (Int.fract (z+t))
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply lintegral_congr
      intro t
      have hm : Measurable (fun s => ENNReal.ofReal (samplingSecondWeight h α s t)*F s) :=
        ((hwm.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal).mul hF
      rw [← (unitInterval_rotate_preserving t).lintegral_comp hm]
      apply lintegral_congr_ae
      filter_upwards [show ∀ᵐ z ∂unitIntervalMeasure, z ∈ Set.Ico (0 : ℝ) 1 from
        ae_restrict_mem measurableSet_Ico] with z hz
      simp only [samplingSecondWeight,sampling_fract_inverse z t hz]
    _ = ∫⁻ z, ∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (Int.fract (z+t))
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply lintegral_lintegral_swap
      exact (((samplingWeight_measurable false h α).comp measurable_swap).ennreal_ofReal.mul
        (hF.comp (sourceFract_measurable.comp (measurable_snd.add measurable_fst)))).aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [show ∀ᵐ z ∂unitIntervalMeasure, z ∈ Set.Ico (0 : ℝ) 1 from
        ae_restrict_mem measurableSet_Ico] with z hz
      apply lintegral_congr
      intro t
      by_cases hw : samplingWeight false h α z t = 0
      · simp [hw]
      · rw [(samplingWeight_orders false h α z t hh hh1 hα hz hw).1]

/-- The actual cutoff second marginal is dominated almost everywhere by
q_h, completing the missing connection to the quadratic ideal moment. -/
theorem samplingSecondDensity_le_ideal (h α : ℝ) (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) :
    ∀ᵐ s ∂unitIntervalMeasure, samplingSecondDensity h α s ≤ samplingIdealSecond h s := by
  have he : ∀ᵐ s ∂unitIntervalMeasure,
      ENNReal.ofReal (samplingSecondDensity h α s) ≤ ENNReal.ofReal (samplingIdealSecond h s) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (samplingSecondDensity_measurable h α).ennreal_ofReal
    intro S hS _
    have hb := samplingWeight_endpoint_domination h α hh hh1 hα (S.indicator (fun _ => 1))
      (measurable_const.indicator hS)
    rw [← samplingSecondDensity_test h α hh hh1 hα _ (measurable_const.indicator hS)] at hb
    have hind (g : ℝ → ℝ≥0∞) : (fun s => g s*S.indicator (fun _ => 1) s) = S.indicator g := by
      funext s
      by_cases hs : s ∈ S <;> simp [Set.indicator,hs]
    rw [hind,hind,lintegral_indicator hS,lintegral_indicator hS] at hb
    exact hb
  filter_upwards [he] with s hs
  exact (ENNReal.ofReal_le_ofReal_iff (samplingIdealSecond_bounds h s hh hh1).1).mp hs

end
end FiniteFactor

end OAI
