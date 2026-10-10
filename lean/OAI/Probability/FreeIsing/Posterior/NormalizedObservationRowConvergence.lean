import OAI.Probability.FreeIsing.Estimates.NormalizedThresholdRowConvergence
import OAI.Probability.FreeIsing.Ising.ObservationComparison

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.NormalizedObservationRows

open IsingObservationInnovation IsingObservationFactor GaussianTreeResponse

variable {d : ℕ}

def rowError (beta : ℝ) (D : Finset (TreeVertex d)) (v w : TreeVertex d)
    (p : ℝ × Paths d) : ℝ :=
  (if w ∈ D then response beta D v w (fun i => p.2 i p.1.toNNReal) else 0) -
    infiniteGibbsResponse beta v w (fun i => p.2 i p.1.toNNReal)

theorem measurable_rowError (beta : ℝ) (D : Finset (TreeVertex d))
    (v w : TreeVertex d) : Measurable (rowError beta D v w) := by
  classical
  have hm : Measurable (fun p : ℝ × Paths d => fun i => p.2 i p.1.toNNReal) :=
    Measurable.of_eval fun i => continuous_eval.measurable.comp
      (((measurable_pi_apply i).comp measurable_snd).prodMk
        (measurable_real_toNNReal.comp measurable_fst))
  unfold rowError
  by_cases hw : w ∈ D
  · simp only [ite_eq_left hw]
    exact ((measurable_response beta D v w).comp hm).sub
      ((measurable_infiniteGibbsResponse beta v w).comp hm)
  · simp only [ite_eq_right hw]
    exact measurable_const.sub ((measurable_infiniteGibbsResponse beta v w).comp hm)

theorem rowError_uniformObservation (beta : ℝ) (D : Finset (TreeVertex d))
    (v w : TreeVertex d) (p : ℝ × IsingInnovation.State d ℝ) (ht : 0 ≤ p.1) :
    rowError beta D v w (p.1, uniformObservation p.2) =
      NormalizedInfiniteTimeEnergy.finiteRow beta D v
        (fun _ t u => WienerSampler.sample u t) w p -
      NormalizedInfiniteTimeEnergy.infiniteRow beta v
        (fun _ t u => WienerSampler.sample u t) w p := by
  have heq : (fun i => uniformObservation p.2 i p.1.toNNReal) =
      (fun i => p.1 * spinSign (p.2.1 i) + WienerSampler.sample (p.2.2 i) p.1.toNNReal) := by
    funext i
    change WienerSampler.sample (p.2.2 i) p.1.toNNReal +
      (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) = _
    rw [Real.coe_toNNReal p.1 ht, add_comm]
  unfold rowError NormalizedInfiniteTimeEnergy.finiteRow
    NormalizedInfiniteTimeEnergy.infiniteRow GaussianTreeResponse.observedRow
  rw [heq]
  rfl

theorem rowError_lintegral_eq
    (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (D : Finset (TreeVertex d)) (v : TreeVertex d) (T : ℝ) :
    (∫⁻ p, ∑' w, ENNReal.ofReal (rowError beta D v w p ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ)) =
    (∫⁻ p, ∑' w, ENNReal.ofReal
      ((NormalizedInfiniteTimeEnergy.finiteRow beta D v
          (fun _ t u => WienerSampler.sample u t) w p -
        NormalizedInfiniteTimeEnergy.infiniteRow beta v
          (fun _ t u => WienerSampler.sample u t) w p) ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (labelMeasure d))) := by
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  let Q := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (labelMeasure d))
  let R := (volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)
  let f : ℝ × Paths d → ℝ≥0∞ := fun p => ∑' w, ENNReal.ofReal (rowError beta D v w p ^ 2)
  have hf : Measurable f := Measurable.tsum fun w =>
    ((measurable_rowError beta D v w).pow_const 2).ennreal_ofReal
  have hobs : MeasurePreserving uniformObservation (μ.prod (labelMeasure d))
      (observationLaw μ) := ⟨measurable_uniformObservation, rfl⟩
  have hp : MeasurePreserving (Prod.map id uniformObservation) Q R :=
    (MeasurePreserving.id _).prod hobs
  change (∫⁻ p, f p ∂ R) = _
  rw [← hp.lintegral_comp hf]
  apply lintegral_congr_ae
  have ht : ∀ᵐ p ∂Q, p.1 ∈ Ioc (0 : ℝ) T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with p hp
  apply tsum_congr
  intro w
  exact congrArg (fun r : ℝ => ENNReal.ofReal (r ^ 2))
    (rowError_uniformObservation beta D v w p hp.1.le)

theorem row_lintegral_tendsto
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hthreshold : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (T : ℝ) :
    Tendsto (fun n => ∫⁻ p, ∑' w, ENNReal.ofReal (rowError beta (D n) v w p ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ)) atTop (𝓝 0) := by
  let := hμ.isProbabilityMeasure
  simp_rw [rowError_lintegral_eq]
  exact NormalizedInfiniteTimeEnergy.finiteRow_threshold_row_lintegral_tendsto
    hd hμ hb hthreshold (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ t => (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample)
    (fun _ => WienerSampler.measurable_sample_eval) D hD hconn hex v hv T

theorem rowError_integrable
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v : TreeVertex d) (hv : v ∈ D) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc 0 T)).prod (observationLaw μ)
    (∀ᵐ p ∂P, Summable (fun w => rowError beta D v w p ^ 2)) ∧
      Integrable (fun p => ∑' w, rowError beta D v w p ^ 2) P ∧
      HasSum (fun w => ∫ p, rowError beta D v w p ^ 2 ∂P)
        (∫ p, ∑' w, rowError beta D v w p ^ 2 ∂P) := by
  let := hμ.isProbabilityMeasure
  let P := (volume.restrict (Ioc 0 T)).prod (observationLaw μ)
  have hf : (∫⁻ p, ∑' w, ENNReal.ofReal (rowError beta D v w p ^ 2) ∂P) ≠ ⊤ := by
    rw [rowError_lintegral_eq]
    exact NormalizedInfiniteTimeEnergy.lintegral_rowError_ne_top hμ hb
      (fun _ : TreeVertex d => uniform01)
      (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
      (fun _ t => (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample)
      (fun _ => WienerSampler.measurable_sample_eval) D hD v hv hT
  rw [lintegral_tsum (fun w =>
    ((measurable_rowError beta D v w).pow_const 2).ennreal_ofReal.aemeasurable)] at hf
  have hm := fun w => (measurable_rowError beta D v w).aestronglyMeasurable (μ := P)
  have hs := ae_summable_sq_of_tsum_lintegral_sq_ne_top P hm hf
  have hi := integrable_tsum_sq_of_tsum_lintegral_sq_ne_top P hm hf
  exact ⟨hs, hi, DiscrepancyEnergy.hasSum_integral_sq_row hm hs hi⟩

theorem row_integral_tendsto
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hthreshold : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc 0 T)).prod (observationLaw μ)
    (∀ n, (∀ᵐ p ∂P, Summable (fun w => rowError beta (D n) v w p ^ 2)) ∧
      Integrable (fun p => ∑' w, rowError beta (D n) v w p ^ 2) P ∧
      HasSum (fun w => ∫ p, rowError beta (D n) v w p ^ 2 ∂P)
        (∫ p, ∑' w, rowError beta (D n) v w p ^ 2 ∂P)) ∧
    Tendsto (fun n => ∫ p, ∑' w, rowError beta (D n) v w p ^ 2 ∂P) atTop (𝓝 0) := by
  let P := (volume.restrict (Ioc 0 T)).prod (observationLaw μ)
  have hvalid (n : ℕ) := rowError_integrable hμ hb (D n) (hconn n) v (hv n) hT
  refine ⟨hvalid, ?_⟩
  have heq (n : ℕ) : (∫ p, ∑' w, rowError beta (D n) v w p ^ 2 ∂P) =
      (∫⁻ p, ∑' w, ENNReal.ofReal (rowError beta (D n) v w p ^ 2) ∂P).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun p => tsum_nonneg fun w => sq_nonneg _)
      (hvalid n).2.1.aestronglyMeasurable]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(hvalid n).1] with p hp
    exact ENNReal.ofReal_tsum_of_nonneg (fun w => sq_nonneg _) hp
  have hlim := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
    (row_lintegral_tendsto hd hμ hb hthreshold D hD hconn hex v hv T)
  change Tendsto (fun n => ∫ p, ∑' w, rowError beta (D n) v w p ^ 2 ∂P) atTop (𝓝 0)
  simp_rw [heq]
  exact hlim

theorem copies_row_lintegral_tendsto
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hthreshold : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (j : Bool) (T : ℝ) :
    Tendsto (fun n => ∫⁻ p, ∑' w, ENNReal.ofReal
      (rowError beta (D n) v w (p.1, if j then p.2.2.1 else p.2.2.2) ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ)) atTop (𝓝 0) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  let pr : Paths d × (Paths d × Paths d) → Paths d :=
    fun q => if j then q.2.1 else q.2.2
  have hpr : MeasurePreserving pr (copies beta μ) (observationLaw μ) := by
    obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
      (beta := beta) (μ := μ)
      (rho := (observationLaw μ).map (innovationMap beta))
      (eta := kernel beta μ) kernel_graphLaw
    cases j
    · exact hr
    · exact hl
  have hp := (MeasurePreserving.id (volume.restrict (Ioc (0 : ℝ) T))).prod hpr
  have heq (n : ℕ) : (∫⁻ p, ∑' w, ENNReal.ofReal
      (rowError beta (D n) v w (p.1, if j then p.2.2.1 else p.2.2.2) ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ)) =
      (∫⁻ p, ∑' w, ENNReal.ofReal (rowError beta (D n) v w p ^ 2)
        ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ)) :=
    hp.lintegral_comp (Measurable.tsum fun w =>
      ((measurable_rowError beta (D n) v w).pow_const 2).ennreal_ofReal)
  simp_rw [heq]
  exact row_lintegral_tendsto hd hμ hb hthreshold D hD hconn hex v hv T

theorem copies_row_integral_tendsto
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hthreshold : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (j : Bool) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc 0 T)).prod (copies beta μ)
    let E := fun n w p => rowError beta (D n) v w
      (p.1, if j then p.2.2.1 else p.2.2.2)
    (∀ n, (∀ᵐ p ∂P, Summable (fun w => E n w p ^ 2)) ∧
      Integrable (fun p => ∑' w, E n w p ^ 2) P) ∧
    Tendsto (fun n => ∫ p, ∑' w, E n w p ^ 2 ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  let pr : Paths d × (Paths d × Paths d) → Paths d :=
    fun q => if j then q.2.1 else q.2.2
  have hpr : MeasurePreserving pr (copies beta μ) (observationLaw μ) := by
    obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
      (beta := beta) (μ := μ)
      (rho := (observationLaw μ).map (innovationMap beta))
      (eta := kernel beta μ) kernel_graphLaw
    cases j
    · exact hr
    · exact hl
  have hp := (MeasurePreserving.id (volume.restrict (Ioc (0 : ℝ) T))).prod hpr
  have ho := row_integral_tendsto hd hμ hb hthreshold D hD hconn hex v hv hT
  refine ⟨fun n => ⟨hp.quasiMeasurePreserving.ae (ho.1 n).1,
    hp.integrable_comp_of_integrable (ho.1 n).2.1⟩, ?_⟩
  have heq (n : ℕ) : (∫ p, ∑' w,
      rowError beta (D n) v w (p.1, if j then p.2.2.1 else p.2.2.2) ^ 2
      ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ)) =
      (∫ p, ∑' w, rowError beta (D n) v w p ^ 2
        ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ)) :=
    hp.hasLaw.integral_comp (ho.1 n).2.1.aestronglyMeasurable
  change Tendsto (fun n => ∫ p, ∑' w,
    rowError beta (D n) v w (p.1, if j then p.2.2.1 else p.2.2.2) ^ 2
    ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ)) atTop (𝓝 0)
  simp_rw [heq]
  exact ho.2

end Problem367.NormalizedObservationRows

end

end OAI
