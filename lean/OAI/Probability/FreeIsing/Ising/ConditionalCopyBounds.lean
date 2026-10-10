import OAI.Probability.FreeIsing.Conditioning.Copies
import OAI.Probability.FreeIsing.Ising.ObservationInnovation
import OAI.Probability.FreeIsing.Posterior.CopyBounds
import OAI.Probability.FreeIsing.Stochastic.ContinuousCopyBrownian

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingConditionalCopyBounds

open PlantedSymmetry IsingObservationInnovation WienerSampler

abbrev CopySpace (d : ℕ) := ContinuousCopyBrownian.Joint (ι := TreeVertex d)

def graphLaw {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin)) :
    Measure (Paths d × Paths d) :=
  (observationLaw μ).map (fun x => (innovationMap beta x, x))

instance graphLaw_isProbabilityMeasure {d : ℕ} (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (graphLaw beta μ) := by
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  unfold graphLaw observationLaw
  infer_instance

theorem hasLaw_observationLaw_eval {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    HasLaw (fun x : Paths d => fun i => x i t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (observationLaw μ) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  have hB (s : ℝ≥0) : Measurable (fun u : ℝ => sample u s) :=
    measurable_sample_eval.comp (measurable_const.prodMk measurable_id)
  let T : IsingInnovation.State d ℝ →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun u i => sample (u i) t)
  have hT : MeasurePreserving T (μ.prod (labelMeasure d))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod
      (brownian_array_eval_measurePreserving (fun _ => uniform01)
        (fun _ => sample_isBrownianReal.toIsPreBrownianReal) (fun _ => hB) t)
  have heval : Measurable (fun x : Paths d => fun i => x i t) :=
    Measurable.of_eval (fun i => (continuous_eval_const t).measurable.comp
      (measurable_pi_apply i))
  refine ⟨heval.aemeasurable, ?_⟩
  rw [observationLaw, Measure.map_map heval measurable_uniformObservation]
  have heq : (fun q : IsingInnovation.State d ℝ => fun i => uniformObservation q i t) =
      observation t ∘ T := by
    funext q i
    change sample (q.2 i) t + (t : ℝ) * spinSign (q.1 i) =
      (t : ℝ) * spinSign (q.1 i) + sample (q.2 i) t
    ring
  change (μ.prod (labelMeasure d)).map
    (fun q : IsingInnovation.State d ℝ => fun i => uniformObservation q i t) = _
  rw [heq, ← Measure.map_map (measurable_observation t) hT.measurable, hT.map_eq]

theorem progressive_leftObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.1 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_fst.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.1 v).continuous)

theorem progressive_rightObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.2 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_snd.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.2 v).continuous)

def fieldDifference {d : ℕ} (beta : ℝ) (v : TreeVertex d) (t : ℝ≥0)
    (q : CopySpace d) : ℝ :=
  Real.artanh (posterior beta v t q.2.1) - Real.artanh (posterior beta v t q.2.2)

section Copies

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
variable {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]

theorem measurePreserving_observation_copies
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    MeasurePreserving (fun q : CopySpace d => q.2.1)
      (rho ⊗ₘ (eta ×ₖ eta)) (observationLaw μ) ∧
    MeasurePreserving (fun q : CopySpace d => q.2.2)
      (rho ⊗ₘ (eta ×ₖ eta)) (observationLaw μ) := by
  have hsecond : MeasurePreserving (Prod.snd : Paths d × Paths d → Paths d)
      (rho ⊗ₘ eta) (observationLaw μ) := by
    refine ⟨measurable_snd, ?_⟩
    have hm : Measurable (fun x : Paths d => (innovationMap beta x, x)) :=
      (measurable_innovationMap beta).prodMk measurable_id
    rw [hjoint, graphLaw, Measure.map_map measurable_snd hm]
    exact Measure.map_id
  have hl := hsecond.comp (measurePreserving_conditionalCopy_fst rho eta)
  have hr := hsecond.comp (measurePreserving_conditionalCopy_snd rho eta)
  exact ⟨hl, hr⟩

theorem ae_innovationMap_copies (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta),
      innovationMap beta q.2.1 = q.1 ∧ innovationMap beta q.2.2 = q.1 := by
  have hgraph : ∀ᵐ q : Paths d × Paths d ∂rho ⊗ₘ eta,
      innovationMap beta q.2 = q.1 := by
    rw [hjoint, graphLaw]
    apply (ae_map_iff
      ((measurable_innovationMap beta).prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun
        ((measurable_innovationMap beta).comp measurable_snd) measurable_fst)).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  have hleft := (measurePreserving_conditionalCopy_fst rho eta).quasiMeasurePreserving.ae hgraph
  have hright := (measurePreserving_conditionalCopy_snd rho eta).quasiMeasurePreserving.ae hgraph
  filter_upwards [hleft, hright] with q hl hr
  exact ⟨hl, hr⟩

theorem identDistrib_observation_copies
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) :
    IdentDistrib (fun q : CopySpace d => fun i => q.2.1 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    IdentDistrib (fun q : CopySpace d => fun i => q.2.2 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨hl, hr⟩ := measurePreserving_observation_copies hjoint
  have heval := hasLaw_observationLaw_eval μ t
  have hobs : HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(measurable_observation t).aemeasurable, rfl⟩
  exact ⟨(heval.comp hl.hasLaw).identDistrib hobs,
    (heval.comp hr.hasLaw).identDistrib hobs⟩

theorem ae_all_innovation_identities (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta), ∀ v t,
      q.2.1 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q ∧
      q.2.2 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q := by
  filter_upwards [ae_innovationMap_copies hjoint] with q hq
  intro v t
  have hl := congrArg (fun x : Paths d => x v t) hq.1
  have hr := congrArg (fun x : Paths d => x v t) hq.2
  change q.2.1 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q = q.1 v t at hl
  change q.2.2 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q = q.1 v t at hr
  constructor <;> linarith

theorem ae_initial_observation_eq (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta),
      (fun v => q.2.1 v 0) = (fun v => q.2.2 v 0) := by
  filter_upwards [ae_all_innovation_identities hjoint] with q hq
  funext v
  have hl := (hq v 0).1
  have hr := (hq v 0).2
  simp only [nnrealTimePrimitive, NNReal.coe_zero,
    intervalIntegral.integral_same, add_zero] at hl hr
  exact hl.trans hr.symm

theorem ae_initial_fieldDifference_zero (hjoint : rho ⊗ₘ eta = graphLaw beta μ)
    (v : TreeVertex d) :
    fieldDifference beta v 0 =ᵐ[rho ⊗ₘ (eta ×ₖ eta)] 0 := by
  filter_upwards [ae_initial_observation_eq hjoint] with q hq
  simp only [fieldDifference, IsingObservationInnovation.posterior, Pi.zero_apply]
  rw [hq, sub_self]

theorem initial_fieldDifference_secondMoment_zero
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (v : TreeVertex d) :
    (∫ q, (fieldDifference beta v 0 q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) = 0 := by
  have hzero := ae_initial_fieldDifference_zero hjoint v
  have heq : (fun q => (fieldDifference beta v 0 q) ^ 2) =ᵐ[rho ⊗ₘ (eta ×ₖ eta)]
      (fun _ => (0 : ℝ)) := hzero.mono (fun q hq => by simp [hq])
  rw [integral_congr_ae heq, integral_zero]

theorem ae_fieldDifference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ q ∂rho ⊗ₘ (eta ×ₖ eta),
      |fieldDifference beta v t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  obtain ⟨hl, hr⟩ := identDistrib_observation_copies hμ hjoint t
  have hx := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  simpa only [fieldDifference, IsingObservationInnovation.posterior] using
    hμ.gibbsField_copy_bound_of_shared_innovation hbeta
      progressive_leftObservation progressive_rightObservation t v hl hr hx hx'

theorem fieldDifference_secondMoment_bounds
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) (v : TreeVertex d) :
    MemLp (fieldDifference beta v t) 2 (rho ⊗ₘ (eta ×ₖ eta)) ∧
      0 ≤ (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ∧
      (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ≤
        (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
  obtain ⟨hl, hr⟩ := identDistrib_observation_copies hμ hjoint t
  have hx := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  exact hμ.gibbsField_copy_secondMoment_bounds hbeta
      progressive_leftObservation progressive_rightObservation t v hl hr hx hx'

theorem fieldDifference_joint_bounds
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (T : ℝ≥0) (v : TreeVertex d) :
    (∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (rho ⊗ₘ (eta ×ₖ eta)),
      |fieldDifference beta v p.1.toNNReal p.2| ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta) ∧
    MemLp (fun p : ℝ × CopySpace d => fieldDifference beta v p.1.toNNReal p.2) 2
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (rho ⊗ₘ (eta ×ₖ eta))) := by
  have hlaws := identDistrib_observation_copies hμ hjoint
  have hx (t : ℝ≥0) :=
    (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' (t : ℝ≥0) :=
    (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  simpa only [fieldDifference, IsingObservationInnovation.posterior] using
    hμ.gibbsField_copy_joint_bounds hbeta progressive_leftObservation
      progressive_rightObservation T v (fun t _ => (hlaws t).1)
      (fun t _ => (hlaws t).2) (fun t _ => hx t) (fun t _ => hx' t)

end Copies

theorem canonical_fieldDifference_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    letI : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
    let R := graphLaw beta μ
    ∀ᵐ q ∂ R.fst ⊗ₘ (R.condKernel ×ₖ R.condKernel),
      |fieldDifference beta v t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact ae_fieldDifference_bound hμ hbeta
    (Measure.disintegrate (graphLaw beta μ) (graphLaw beta μ).condKernel) t v

end Problem367.IsingConditionalCopyBounds

end

end OAI
