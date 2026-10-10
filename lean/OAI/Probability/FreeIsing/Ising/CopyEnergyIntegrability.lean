import OAI.Probability.FreeIsing.Energy.DiscrepancyRowEnergy
import OAI.Probability.FreeIsing.Energy.NormalizedInfiniteTimeEnergy
import OAI.Probability.FreeIsing.Ising.ObservationComparison
import OAI.Probability.FreeIsing.Ising.ObservationPosteriorTransport

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.IsingCopyEnergy
open IsingObservationInnovation IsingObservationFactor

def responseRow {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (p : ℝ × Paths d) : ℝ :=
  infiniteGibbsResponse beta v w (fun i => p.2 i p.1.toNNReal)

theorem measurable_responseRow {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (responseRow beta v w) := by
  apply (measurable_infiniteGibbsResponse beta v w).comp
  apply Measurable.of_eval
  intro i
  exact continuous_eval.measurable.comp
    (((measurable_pi_apply i).comp measurable_snd).prodMk
      (measurable_real_toNNReal.comp measurable_fst))

theorem observation_extended_energy_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ p, ∑' w, ENNReal.ofReal (responseRow beta v w p ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ)) ≤
      ENNReal.ofReal (2 * ((d : ℝ) * beta + T + Real.sqrt T)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  let Q := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (labelMeasure d))
  let R := (volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)
  let f : ℝ × Paths d → ℝ≥0∞ := fun p => ∑' w, ENNReal.ofReal (responseRow beta v w p ^ 2)
  have hf : Measurable f := Measurable.tsum (fun w =>
    ((measurable_responseRow beta v w).pow_const 2).ennreal_ofReal)
  have hmp : MeasurePreserving (Prod.map id uniformObservation) Q R :=
    (MeasurePreserving.id _).prod (measurePreserving_uniformObservation μ)
  have henergy := NormalizedInfiniteTimeEnergy.lintegral_infiniteRow_le hμ hb
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ t => (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample)
    (fun _ => WienerSampler.measurable_sample_eval) v hT
  have heq : (fun p => f (Prod.map id uniformObservation p)) =ᵐ[Q]
      (fun p => ∑' w, ENNReal.ofReal
        (NormalizedInfiniteTimeEnergy.infiniteRow beta v
          (fun _ t u => WienerSampler.sample u t) w p ^ 2)) := by
    have hmem : ∀ᵐ p ∂Q, p.1 ∈ Ioc (0 : ℝ) T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    apply tsum_congr
    intro w
    apply congrArg ENNReal.ofReal
    apply congrArg (fun r : ℝ => r ^ 2)
    change infiniteGibbsResponse beta v w (fun i => uniformObservation p.2 i p.1.toNNReal) = _
    apply congrArg (infiniteGibbsResponse beta v w)
    funext i
    change WienerSampler.sample (p.2.2 i) p.1.toNNReal +
      (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) =
        p.1 * spinSign (p.2.1 i) + WienerSampler.sample (p.2.2 i) p.1.toNNReal
    rw [Real.coe_toNNReal p.1 hp.1.le, add_comm]
  calc
    _ = ∫⁻ p, f (Prod.map id uniformObservation p) ∂Q := (hmp.lintegral_comp hf).symm
    _ = _ := lintegral_congr_ae heq
    _ ≤ _ := henergy

theorem observation_row_energy_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    (∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ),
      Summable (fun w => responseRow beta v w p ^ 2)) ∧
    Integrable (fun p => ∑' w, responseRow beta v w p ^ 2)
      ((volume.restrict (Ioc 0 T)).prod (observationLaw μ)) ∧
    (∫ p, ∑' w, responseRow beta v w p ^ 2
      ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ)) ≤
      2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)
  have he := observation_extended_energy_le hμ hb v hT
  rw [lintegral_tsum (fun w =>
    ((measurable_responseRow beta v w).pow_const 2).ennreal_ofReal.aemeasurable)] at he
  have hm (w : TreeVertex d) : AEStronglyMeasurable (responseRow beta v w) P :=
    (measurable_responseRow beta v w).aestronglyMeasurable
  exact ⟨ae_summable_sq_of_tsum_lintegral_sq_ne_top P hm
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top he),
    integral_tsum_sq_le_of_tsum_lintegral_sq_le P hm (by positivity) he⟩

abbrev Joint (d : ℕ) := Paths d × (Paths d × Paths d)

def projection {d : ℕ} (j : Bool) (q : Joint d) : Paths d :=
  if j then q.2.1 else q.2.2

private theorem projection_measurePreserving
    {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (j : Bool) :
    MeasurePreserving (projection (d := d) j) (copies beta μ) (observationLaw μ) := by
  obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
    (beta := beta) (μ := μ)
    (rho := (observationLaw μ).map (innovationMap beta)) (eta := kernel beta μ) kernel_graphLaw
  cases j
  · exact hr
  · exact hl

def timeProjection {d : ℕ} (j : Bool) (p : ℝ × Joint d) : ℝ × Paths d :=
  (p.1, projection j p.2)

private theorem timeProjection_measurePreserving
    {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (j : Bool) (T : ℝ) :
    MeasurePreserving (timeProjection (d := d) j)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ))
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) :=
  (MeasurePreserving.id _).prod (projection_measurePreserving beta μ j)

theorem copy_row_energy_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (j : Bool) {T : ℝ} (hT : 0 ≤ T) :
    (∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ),
      Summable (fun w => responseRow beta v w (timeProjection j p) ^ 2)) ∧
    Integrable (fun p => ∑' w, responseRow beta v w (timeProjection j p) ^ 2)
      ((volume.restrict (Ioc 0 T)).prod (copies beta μ)) ∧
    (∫ p, ∑' w, responseRow beta v w (timeProjection j p) ^ 2
      ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ)) ≤
      2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  have ho := observation_row_energy_integrable hμ hb v hT
  have hp := timeProjection_measurePreserving beta μ j T
  refine ⟨hp.quasiMeasurePreserving.ae ho.1, hp.integrable_comp_of_integrable ho.2.1, ?_⟩
  simpa only [Function.comp_def] using
    (hp.hasLaw.integral_comp ho.2.1.aestronglyMeasurable).le.trans ho.2.2

def density {d : ℕ} (beta : ℝ) (v : TreeVertex d) (t : ℝ) (q : Joint d) : ℝ :=
  DiscrepancyEnergy.density
    (fun w q => responseRow beta v w (t, q.2.1))
    (fun w q => responseRow beta v w (t, q.2.2))
    (fun q => field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2)
    (fun q => posterior beta v t.toNNReal q.2.1)
    (fun q => posterior beta v t.toNNReal q.2.2) q

theorem density_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => density beta v p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ)) := by
  have hl := copy_row_energy_integrable hμ hb v true T.coe_nonneg
  have hr := copy_row_energy_integrable hμ hb v false T.coe_nonneg
  have hmap (j : Bool) : Measurable (fun p : ℝ × Joint d =>
      (p.1.toNNReal, projection j p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk
      ((projection_measurePreserving beta μ j).measurable.comp measurable_snd)
  have hbound := (IsingConditionalCopyBounds.fieldDifference_joint_bounds
    hμ hb kernel_graphLaw T v).1
  apply DiscrepancyEnergy.integrable_noise_add_drift
    (c := fun w p => responseRow beta v w (timeProjection true p))
    (c' := fun w p => responseRow beta v w (timeProjection false p))
    (H := 2 * (T : ℝ) + 2 * (d : ℝ) * beta)
    (fun w => ((measurable_responseRow beta v w).comp
      (timeProjection_measurePreserving beta μ true T).measurable).aestronglyMeasurable)
    (fun w => ((measurable_responseRow beta v w).comp
      (timeProjection_measurePreserving beta μ false T).measurable).aestronglyMeasurable)
    (((measurable_field_joint beta v).comp (hmap true)).sub
      ((measurable_field_joint beta v).comp (hmap false))).aestronglyMeasurable
    (((measurable_posterior_joint beta v).comp (hmap true)).aestronglyMeasurable)
    (((measurable_posterior_joint beta v).comp (hmap false)).aestronglyMeasurable)
    hl.2.1 hr.2.1 (hl.1.and hr.1)
  filter_upwards [hbound] with p hp
  exact ⟨hp, posterior_norm_le_one beta v p.1.toNNReal p.2.2.1,
    posterior_norm_le_one beta v p.1.toNNReal p.2.2.2⟩

theorem ae_integral_density_eq
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (T : ℝ≥0) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      (∫ q, density beta v t q ∂copies beta μ) =
        (∑' w, ∫ q, (responseRow beta v w (t, q.2.1) -
          responseRow beta v w (t, q.2.2)) ^ 2 ∂copies beta μ) +
        2 * ∫ q, (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) *
          (posterior beta v t.toNNReal q.2.1 * (∑' w, responseRow beta v w (t, q.2.1) ^ 2) -
            posterior beta v t.toNNReal q.2.2 * (∑' w, responseRow beta v w (t, q.2.2) ^ 2))
            ∂copies beta μ := by
  have hl := copy_row_energy_integrable hμ hb v true T.coe_nonneg
  have hr := copy_row_energy_integrable hμ hb v false T.coe_nonneg
  rw [← restrict_Ioc_eq_restrict_Icc]
  filter_upwards [hl.2.1.prod_right_ae, hr.2.1.prod_right_ae,
    Measure.ae_ae_of_ae_prod hl.1, Measure.ae_ae_of_ae_prod hr.1] with t hAl hAr hsl hsr
  have hmap (j : Bool) : Measurable (fun q : Joint d => (t.toNNReal, projection j q)) :=
    measurable_const.prodMk (projection_measurePreserving beta μ j).measurable
  have hrow (j : Bool) (w : TreeVertex d) :
      Measurable (fun q : Joint d => responseRow beta v w (t, projection j q)) :=
    (measurable_responseRow beta v w).comp
      (measurable_const.prodMk (projection_measurePreserving beta μ j).measurable)
  apply DiscrepancyEnergy.integral_noise_add_drift
    (H := 2 * (t.toNNReal : ℝ) + 2 * (d : ℝ) * beta)
    (fun w => (hrow true w).aestronglyMeasurable)
    (fun w => (hrow false w).aestronglyMeasurable)
    (((measurable_field_joint beta v).comp (hmap true)).sub
      ((measurable_field_joint beta v).comp (hmap false))).aestronglyMeasurable
    (((measurable_posterior_joint beta v).comp (hmap true)).aestronglyMeasurable)
    (((measurable_posterior_joint beta v).comp (hmap false)).aestronglyMeasurable)
    hAl hAr (hsl.and hsr)
  filter_upwards [IsingConditionalCopyBounds.ae_fieldDifference_bound
    hμ hb kernel_graphLaw t.toNNReal v] with q hq
  exact ⟨hq, posterior_norm_le_one beta v t.toNNReal q.2.1,
    posterior_norm_le_one beta v t.toNNReal q.2.2⟩

end Problem367.IsingCopyEnergy

end

end OAI
