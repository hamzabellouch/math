import OAI.Analysis.FiniteFactor.Sampling.WeightTransport

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- ENNReal form of the constructed averaged density. -/
theorem samplingIdealSecond_lintegral (h s : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    ENNReal.ofReal (samplingIdealSecond h s) =
      ∫⁻ v, ENNReal.ofReal (samplingTransportDensity v s) ∂samplingVelocityMeasure h := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have hm : Measurable (fun v => samplingTransportDensity v s) :=
    samplingTransportDensity_measurable.comp (measurable_id.prodMk measurable_const)
  have hqi : Integrable (fun v => samplingTransportDensity v s) (samplingVelocityMeasure h) :=
    (integrable_const (1/(1-h))).mono' hm.aestronglyMeasurable (by
      filter_upwards [hv] with v hv
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1]
      exact (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.1)
  exact ofReal_integral_eq_lintegral_ofReal hqi (hv.mono (fun v hv =>
    (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1))

/-- The average of the actual transport laws has density q_h. -/
theorem samplingTransport_average (h : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, ∫⁻ v, F (samplingTransport v z) ∂samplingVelocityMeasure h ∂unitIntervalMeasure) =
      ∫⁻ s, ENNReal.ofReal (samplingIdealSecond h s)*F s ∂unitIntervalMeasure := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have htm : Measurable (fun p : ℝ × ℝ => samplingTransport p.2 p.1) := by
    unfold samplingTransport samplingDistance
    fun_prop
  have hswap := lintegral_lintegral_swap (μ := unitIntervalMeasure) (ν := samplingVelocityMeasure h) (f := fun z v => F (samplingTransport v z)) (hF.comp htm).aemeasurable
  rw [hswap]
  calc
    _ = ∫⁻ v, (∫⁻ s, ENNReal.ofReal (samplingTransportDensity v s)*F s ∂unitIntervalMeasure)
        ∂samplingVelocityMeasure h := by
      apply lintegral_congr_ae
      filter_upwards [hv] with v hv
      have hm : Measurable (samplingTransport v) := by unfold samplingTransport samplingDistance; fun_prop
      rw [← lintegral_map hF hm,samplingTransport_density v hv.1.le (hv.2.trans_lt hh1)]
      have hmd : Measurable (fun s => ENNReal.ofReal (samplingTransportDensity v s)) :=
        (samplingTransportDensity_measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
      exact lintegral_withDensity_eq_lintegral_mul unitIntervalMeasure hmd hF
    _ = ∫⁻ s, (∫⁻ v, ENNReal.ofReal (samplingTransportDensity v s)*F s ∂samplingVelocityMeasure h)
        ∂unitIntervalMeasure := lintegral_lintegral_swap
          (samplingTransportDensity_measurable.ennreal_ofReal.mul (hF.comp measurable_snd)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro s
      have hmd : Measurable (fun v => ENNReal.ofReal (samplingTransportDensity v s)) :=
        (samplingTransportDensity_measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
      rw [lintegral_mul_const _ hmd,← samplingIdealSecond_lintegral h s hh hh1]

/-- An actual cutoff-weight endpoint estimate, with no assumed second-marginal
identification. It holds against every measurable nonnegative test. -/
theorem samplingWeight_endpoint_domination (h α : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, ∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t)
      ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤
        ∫⁻ s, ENNReal.ofReal (samplingIdealSecond h s)*F s ∂unitIntervalMeasure := by
  rw [← samplingTransport_average h hh hh1 F hF]
  apply lintegral_mono_ae
  filter_upwards [show ∀ᵐ z ∂unitIntervalMeasure, z ∈ Set.Ico (0 : ℝ) 1 from
    ae_restrict_mem measurableSet_Ico] with z hz
  exact samplingWeight_transport_le h α z hh hh1 hα hz F hF

end
end FiniteFactor

end OAI
