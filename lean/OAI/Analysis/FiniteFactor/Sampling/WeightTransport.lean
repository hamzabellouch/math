import OAI.Analysis.FiniteFactor.Sampling.SecondMoment

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- At each retained starting coordinate, the source weight is exactly the
law of the displacement v times the distance to the endpoint. -/
theorem samplingWeight_displacement (h α z : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (hcut : α ≤ samplingDistance z) :
    unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (samplingWeight false h α z t)) =
      (samplingVelocityMeasure h).map (fun v => samplingDistance z * v) := by
  let d := samplingDistance z
  have hd : 0 < d := hα.trans_le hcut
  have hL : 0 < h*d := mul_pos hh hd
  have hd1 : d ≤ 1-z := min_le_right _ _
  have hL1 : h*d ≤ 1 := by nlinarith [hz.1]
  have he : (fun t => ENNReal.ofReal (samplingWeight false h α z t)) =
      (Set.Ioo 0 (h*d)).indicator (fun _ => ENNReal.ofReal (1/(h*d))) := by
    funext t
    simp only [samplingWeight,Bool.false_eq_true,ite_false,hcut,true_and,Set.indicator,Set.mem_Ioo,d]
    split_ifs <;> simp
  rw [he,withDensity_indicator measurableSet_Ioo,withDensity_const]
  unfold unitIntervalMeasure
  rw [Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_left.mpr (show Set.Ioo 0 (h*d) ⊆ Set.Ico (0 : ℝ) 1 from
      fun t ht => ⟨ht.1.le,ht.2.trans_le hL1⟩),restrict_Ioo_eq_restrict_Ioc]
  unfold samplingVelocityMeasure ProbabilityTheory.cond
  rw [Measure.map_smul _ (by fun_prop)]
  have ha := map_interval_affine 0 h d 0 hd
  simp only [mul_zero,add_zero] at ha
  rw [ha,smul_smul,Real.volume_Ioc,sub_zero]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos hh,← ENNReal.ofReal_mul (inv_nonneg.mpr hh.le)]
  congr 1
  dsimp [d]
  field_simp
  simp [mul_comm]

/-- Exact substitution t=v*Delta(z), at each retained starting point. -/
theorem samplingWeight_transport_integral (h α z : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (hcut : α ≤ samplingDistance z)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t) ∂unitIntervalMeasure) =
      ∫⁻ v, F (samplingTransport v z) ∂samplingVelocityMeasure h := by
  have hw : Measurable (fun t => ENNReal.ofReal (samplingWeight false h α z t)) :=
    ((samplingWeight_measurable false h α).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hFz : Measurable (fun t => F (z+t)) := hF.comp (by fun_prop)
  have hi := lintegral_withDensity_eq_lintegral_mul unitIntervalMeasure hw hFz
  simp only [Pi.mul_apply] at hi
  rw [← hi,
    samplingWeight_displacement h α z hh hh1 hα hz hcut,
    lintegral_map hFz (by fun_prop)]
  apply lintegral_congr
  intro v
  simp [samplingTransport,mul_comm]

/-- Discarding the cutoff only increases the weighted endpoint law. -/
theorem samplingWeight_transport_le (h α z : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t) ∂unitIntervalMeasure) ≤
      ∫⁻ v, F (samplingTransport v z) ∂samplingVelocityMeasure h := by
  by_cases hc : α ≤ samplingDistance z
  · exact (samplingWeight_transport_integral h α z hh hh1 hα hz hc F hF).le
  · simp [samplingWeight,hc]

end
end FiniteFactor

end OAI
