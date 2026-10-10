import OAI.Probability.FreeIsing.Ising.ObservationResponseEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.IsingObservationResponseEnergy

open IsingObservationInnovation IsingObservationFactor CriticalCanonicalRowEnergy

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def timeEnergyConstant (d : ℕ) (beta : ℝ) : ℝ :=
  1 + (d : ℝ) * Real.tanh beta ^ 2 /
    ComponentSignalAttenuation.lossCoefficient (Real.tanh beta)

theorem row_bound_le_time_majorant
    (hb : 0 ≤ beta) (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ} (ht : 0 < t) :
    1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t.toNNReal ≤
      timeEnergyConstant d beta * (1 + t ^ (-(1 : ℝ) / 2)) := by
  have hC : 0 < ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) := by
    simpa [rate] using (rate_pos hb hc (by norm_num : (0 : ℝ≥0) < 1))
  have hK : 0 ≤ (d : ℝ) * Real.tanh beta ^ 2 /
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) := by positivity
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hp : t ^ (-(1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg ht.le,
      ← Real.sqrt_eq_rpow]
  rw [hp]
  unfold rate timeEnergyConstant
  rw [Real.coe_toNNReal t ht.le]
  by_cases hs1 : Real.sqrt t ≤ 1
  · rw [min_eq_left hs1, div_mul_eq_div_mul_one_div, one_div]
    nlinarith [inv_nonneg.mpr hs.le]
  · rw [min_eq_right (le_of_not_ge hs1), mul_one]
    nlinarith [inv_nonneg.mpr hs.le]

theorem integrable_time_majorant (d : ℕ) (beta : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun t : ℝ => timeEnergyConstant d beta * (1 + t ^ (-(1 : ℝ) / 2)))
      (volume.restrict (Ioc 0 T)) := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  exact ((integrable_const (1 : ℝ)).add
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hp)).const_mul _

theorem integrable_response_row_time
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (u : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun p : ℝ × Paths d => ∑' v, response beta u v p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc 0 T)).prod (observationLaw μ)) := by
  have hm : Measurable (fun p : ℝ × Paths d => ∑' v,
      response beta u v p.1.toNNReal p.2 ^ 2) := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.tsum
    intro v
    exact (((measurable_response_joint beta u v).comp
      (measurable_real_toNNReal.prodMap measurable_id)).pow_const 2).stronglyMeasurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (response_row_energy hμ hb hd hc (Real.toNNReal_pos.mpr ht.1) u).2.1
  · apply (integrable_time_majorant d beta hT).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hn (x : Paths d) : 0 ≤ ∑' v, response beta u v t.toNNReal x ^ 2 :=
      tsum_nonneg (fun v => sq_nonneg _)
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    rw [abs_of_nonneg (integral_nonneg hn)]
    exact (response_row_energy hμ hb hd hc (Real.toNNReal_pos.mpr ht.1) u).2.2.trans
      (row_bound_le_time_majorant hb hc ht.1)

theorem integrable_copy_response_row_time
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (u : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) (j : Bool) :
    Integrable (fun p : ℝ × (Paths d × (Paths d × Paths d)) => ∑' v,
      response beta u v p.1.toNNReal (copyObservation j p.2) ^ 2)
      ((volume.restrict (Ioc 0 T)).prod (copies beta μ)) :=
  ((MeasurePreserving.id (volume.restrict (Ioc 0 T))).prod
    (measurePreserving_copyObservation (beta := beta) (μ := μ) j)).integrable_comp_of_integrable
      (integrable_response_row_time hμ hb hd hc u hT)

theorem integral_time_majorant (d : ℕ) (beta : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Ioc 0 T, timeEnergyConstant d beta * (1 + t ^ (-(1 : ℝ) / 2))) =
      timeEnergyConstant d beta * (T + 2 * Real.sqrt T) := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [integral_const_mul]
  congr 1
  rw [← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_add intervalIntegrable_const hp,
    intervalIntegral.integral_const, integral_rpow (Or.inl (by norm_num))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

theorem lintegral_response_row_time_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (u : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ p : ℝ × Paths d, ∑' v, ENNReal.ofReal
      (response beta u v p.1.toNNReal p.2 ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ)) ≤
      ENNReal.ofReal (timeEnergyConstant d beta * (T + 2 * Real.sqrt T)) := by
  have hm : Measurable (fun p : ℝ × Paths d => ∑' v, ENNReal.ofReal
      (response beta u v p.1.toNNReal p.2 ^ 2)) :=
    Measurable.tsum fun v => (((measurable_response_joint beta u v).comp
      (measurable_real_toNNReal.prodMap measurable_id)).pow_const 2).ennreal_ofReal
  have hC : 0 < ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) := by
    simpa [rate] using (rate_pos hb hc (by norm_num : (0 : ℝ≥0) < 1))
  have hK : 0 ≤ timeEnergyConstant d beta := by
    unfold timeEnergyConstant
    positivity
  calc
    _ = ∫⁻ t in Ioc 0 T, ∫⁻ x, ∑' v, ENNReal.ofReal
        (response beta u v t.toNNReal x ^ 2) ∂observationLaw μ :=
      lintegral_prod _ hm.aemeasurable
    _ ≤ ∫⁻ t in Ioc 0 T,
        ENNReal.ofReal (timeEnergyConstant d beta * (1 + t ^ (-(1 : ℝ) / 2))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (lintegral_response_row_le hμ hb hd hc (Real.toNNReal_pos.mpr ht.1) u).trans
        (ENNReal.ofReal_le_ofReal (row_bound_le_time_majorant hb hc ht.1))
    _ = ENNReal.ofReal (∫ t in Ioc 0 T,
        timeEnergyConstant d beta * (1 + t ^ (-(1 : ℝ) / 2))) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal (integrable_time_majorant d beta hT)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg hK (add_nonneg zero_le_one (Real.rpow_nonneg ht.1.le _))
    _ = _ := congrArg ENNReal.ofReal (integral_time_majorant d beta hT)

theorem lintegral_copy_response_row_time_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (u : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) (j : Bool) :
    (∫⁻ p : ℝ × (Paths d × (Paths d × Paths d)), ∑' v, ENNReal.ofReal
      (response beta u v p.1.toNNReal (copyObservation j p.2) ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ)) ≤
      ENNReal.ofReal (timeEnergyConstant d beta * (T + 2 * Real.sqrt T)) := by
  have hp := (MeasurePreserving.id (volume.restrict (Ioc 0 T))).prod
    (measurePreserving_copyObservation (beta := beta) (μ := μ) j)
  have hm : Measurable (fun p : ℝ × Paths d => ∑' v, ENNReal.ofReal
      (response beta u v p.1.toNNReal p.2 ^ 2)) :=
    Measurable.tsum fun v => (((measurable_response_joint beta u v).comp
      (measurable_real_toNNReal.prodMap measurable_id)).pow_const 2).ennreal_ofReal
  exact (hp.hasLaw.lintegral_comp hm.aemeasurable).trans_le
    (lintegral_response_row_time_le hμ hb hd hc u hT)

theorem tendsto_copy_response_row_time_zero
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (u : TreeVertex d) (j : Bool) :
    Tendsto (fun T : ℝ≥0 => ∫⁻ p : ℝ × (Paths d × (Paths d × Paths d)),
      ∑' v, ENNReal.ofReal (response beta u v p.1.toNNReal (copyObservation j p.2) ^ 2)
      ∂(volume.restrict (Ioc 0 (T : ℝ))).prod (copies beta μ)) (𝓝 0) (𝓝 0) := by
  have hcont : Continuous (fun T : ℝ≥0 => ENNReal.ofReal
      (timeEnergyConstant d beta * ((T : ℝ) + 2 * Real.sqrt (T : ℝ)))) :=
    ENNReal.continuous_ofReal.comp
      (continuous_const.mul (NNReal.continuous_coe.add
        (continuous_const.mul (Real.continuous_sqrt.comp NNReal.continuous_coe))))
  have hlim : Tendsto (fun T : ℝ≥0 => ENNReal.ofReal
      (timeEnergyConstant d beta * ((T : ℝ) + 2 * Real.sqrt (T : ℝ)))) (𝓝 0) (𝓝 0) := by
    simpa only [NNReal.coe_zero, Real.sqrt_zero, mul_zero, add_zero, ENNReal.ofReal_zero]
      using hcont.tendsto 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
    (Eventually.of_forall fun T => lintegral_copy_response_row_time_le hμ hb hd hc u T.property j)

end Problem367.IsingObservationResponseEnergy

end

end OAI
