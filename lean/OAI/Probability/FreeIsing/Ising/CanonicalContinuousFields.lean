import OAI.Probability.FreeIsing.Estimates.ProgressiveVersionPushforward
import OAI.Probability.FreeIsing.Ising.ContinuousPosterior
import OAI.Probability.FreeIsing.Ising.CopyStoppedEnergy
import OAI.Probability.FreeIsing.Posterior.ContinuousPosteriorInterior

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

def continuousField {d : ℕ} (beta : ℝ) (v : TreeVertex d) : ℝ≥0 → Paths d → ℝ :=
  ProgressiveVersionPushforward.version (field beta v)

lemma field_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (field beta v) :=
  isStronglyProgressive_artanh (filtration d) (posterior_progressive beta v)

lemma continuousField_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousField beta v) :=
  ProgressiveVersionPushforward.progressive_version (field_progressive beta v)

theorem continuousField_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    (∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousField beta v t x)) ∧
      (∀ t, continuousField beta v t =ᵐ[observationLaw μ] field beta v t) := by
  let B : ℝ≥0 → ℝ → ℝ := fun t u => WienerSampler.sample u t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  have hcB (u : ℝ) : Continuous (fun t => B t u) := (WienerSampler.sample u).continuous
  obtain ⟨Z, hZ⟩ := Classical.axiomOfChoice
    (fun w : TreeVertex d => IsingInnovation.exists_continuous_posterior
      hd hμ hb hcrit uniform01 WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
      hmB hcB w)
  have hcont (w : TreeVertex d) : ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => Z w t q) := (hZ w).2.2.1
  have hver (w : TreeVertex d) (t : ℝ≥0) : Z w t =ᵐ[μ.prod (labelMeasure d)]
      (fun q => infiniteGibbsSpinMean beta w
        (fun i => (t : ℝ) * spinSign (q.1 i) + B t (q.2 i))) := by
    filter_upwards [(hZ w).2.2.2.2.2 t] with q hq
    refine hq.trans ?_
    change infiniteGibbsSpinMean beta w
      (fun i => B t (q.2 i) + (t : ℝ) * spinSign (q.1 i)) = _
    apply congrArg (infiniteGibbsSpinMean beta w)
    funext i
    exact add_comm _ _
  have hfields := hμ.continuous_posterior_all_time_field_bound hb
    (fun _ : TreeVertex d => uniform01) (fun _ => WienerSampler.sample_isBrownianReal)
    (fun _ => hmB) hcont hver
  have hc : ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => Real.artanh (Z v t q)) :=
    hfields.mono (fun q hq => (hq v).2)
  have he (t : ℝ≥0) : (fun q => Real.artanh (Z v t q)) =ᵐ[μ.prod (labelMeasure d)]
      (fun q => field beta v t (uniformObservation q)) := by
    filter_upwards [hver v t] with q hq
    change Real.artanh (Z v t q) = Real.artanh
      (infiniteGibbsSpinMean beta v
        (fun i => B t (q.2 i) + (t : ℝ) * spinSign (q.1 i)))
    apply congrArg Real.artanh
    refine hq.trans ?_
    apply congrArg (infiniteGibbsSpinMean beta v)
    funext i
    exact add_comm _ _
  exact (ProgressiveVersionPushforward.continuous_progressive_version_of_pullback
    measurable_uniformObservation (field_progressive beta v) hc he).2

def continuousDifference {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (q : Paths d × (Paths d × Paths d)) : ℝ :=
  continuousField beta v t q.2.1 - continuousField beta v t q.2.2

lemma continuousDifference_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (continuousDifference beta v) := by
  have hl : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : IsingConditionalCopyBounds.CopySpace d) => field beta v t q.2.1) :=
    isStronglyProgressive_artanh _ (isStronglyProgressive_infiniteGibbsSpinMean _ beta v _
      IsingConditionalCopyBounds.progressive_leftObservation)
  have hr : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : IsingConditionalCopyBounds.CopySpace d) => field beta v t q.2.2) :=
    isStronglyProgressive_artanh _ (isStronglyProgressive_infiniteGibbsSpinMean _ beta v _
      IsingConditionalCopyBounds.progressive_rightObservation)
  exact (ProgressiveVersionPushforward.progressive_version hl).sub
    (ProgressiveVersionPushforward.progressive_version hr)

theorem continuousDifference_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    (∀ᵐ q ∂copies beta μ, Continuous (fun t => continuousDifference beta v t q)) ∧
      (∀ t, continuousDifference beta v t =ᵐ[copies beta μ]
        (fun q => field beta v t q.2.1 - field beta v t q.2.2)) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
    (beta := beta) (μ := μ) (rho := (observationLaw μ).map (innovationMap beta))
    (eta := kernel beta μ) kernel_graphLaw
  obtain ⟨hc, he⟩ := continuousField_modification hd hμ hb hcrit v
  constructor
  · filter_upwards [hl.quasiMeasurePreserving.ae hc, hr.quasiMeasurePreserving.ae hc]
      with q hql hqr
    exact hql.sub hqr
  · intro t
    filter_upwards [hl.quasiMeasurePreserving.ae (he t), hr.quasiMeasurePreserving.ae (he t)]
      with q hql hqr
    exact congrArg₂ (fun x y : ℝ => x - y) hql hqr

end Problem367.IsingObservationFactor

end

end OAI
