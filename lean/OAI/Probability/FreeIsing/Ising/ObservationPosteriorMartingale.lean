import OAI.Probability.FreeIsing.Conditioning.Pullback
import OAI.Probability.FreeIsing.Ising.ObservationPosteriorTransport
import OAI.Probability.FreeIsing.Ising.ObservationRecovery
import OAI.Probability.FreeIsing.Martingales.TransformL2

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation
open IsingObservationRecovery

theorem integrable_decodedSpin {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (v : TreeVertex d) :
    Integrable (fun x : Paths d => spinSign (decode x v)) (observationLaw μ) := by
  have hs : Measurable spinSign := by intro s hs; trivial
  apply Integrable.of_bound
    (hs.comp ((measurable_pi_apply v).comp measurable_decode)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    cases h : decode x v <;> norm_num [spinSign, h]

theorem posterior_eq_condExp_decodedSpin {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) (t : ℝ≥0) :
    posterior beta v t =ᵐ[observationLaw μ]
      (observationLaw μ)[fun x => spinSign (decode x v) | filtration d t] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  have hp := condExp_comp_measurePreserving (μ.prod (labelMeasure d)) (observationLaw μ)
    uniformObservation (measurePreserving_uniformObservation μ) (filtration d t)
    ((filtration d).le t) (integrable_decodedSpin μ v)
  have hd : (fun q : IsingInnovation.State d ℝ => spinSign (decode (uniformObservation q) v)) =ᵐ[
      μ.prod (labelMeasure d)] (fun q => spinSign (q.1 v)) :=
    (decode_uniformObservation_ae μ).fun_comp (fun sigma => spinSign (sigma v))
  have hc := condExp_congr_ae (m := (filtration d t).comap uniformObservation) hd
  have hmB (s : ℝ≥0) : Measurable (fun u => WienerSampler.sample u s) :=
    (continuous_eval_const s).measurable.comp WienerSampler.measurable_sample
  have hactual := hμ.infiniteGibbsSpinMean_eq_brownian_past
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ => hmB) t v
  apply (ae_eq_iff_comp_measurePreserving (μ.prod (labelMeasure d)) (observationLaw μ)
    uniformObservation (measurePreserving_uniformObservation μ)
    (measurable_posterior beta v t)
    ((stronglyMeasurable_condExp.mono ((filtration d).le t)).measurable)).mpr
  filter_upwards [hp, hc, hactual] with q hp hc ha
  change posterior beta v t (uniformObservation q) = _
  simp only [Function.comp_def] at hp ⊢
  rw [← hp, hc]
  rw [filtration_comap_uniformObservation d t hmB]
  simpa only [posterior, uniformObservation, ContinuousMap.coe_mk,
    ArrayPosteriorStationarity.filtration, arrayObservationFiltration,
    arrayNaturalFiltration_eq_comap, plantedArrayObservation,
    ArrayPosteriorStationarity.spinArray, labelMeasure, add_comm] using ha

theorem posterior_martingale {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    Martingale (posterior beta v) (filtration d) (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact (martingale_condExp (fun x => spinSign (decode x v))
    (filtration d) (observationLaw μ)).congr
    (posterior_progressive beta v).stronglyAdapted
    (fun t => (posterior_eq_condExp_decodedSpin hμ v t).symm)

theorem integral_posterior_sq_increment_eq {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ x, (posterior beta v t x - posterior beta v s x) ^ 2 ∂observationLaw μ) =
      (∫ x, posterior beta v t x ^ 2 ∂observationLaw μ) -
        ∫ x, posterior beta v s x ^ 2 ∂observationLaw μ := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact MartingaleTransformL2.integral_sq_increment_eq (posterior_martingale hμ v)
    hst (posterior_memLp beta μ v s 2) (posterior_memLp beta μ v t 2)

theorem posterior_secondMoment_monotone {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    Monotone (fun t : ℝ≥0 => ∫ x, posterior beta v t x ^ 2 ∂observationLaw μ) := by
  intro s t hst
  have hn : (0 : ℝ) ≤ ∫ x, (posterior beta v t x - posterior beta v s x) ^ 2
      ∂observationLaw μ :=
    integral_nonneg (fun x => sq_nonneg (posterior beta v t x - posterior beta v s x))
  rw [integral_posterior_sq_increment_eq hμ v hst] at hn
  exact sub_nonneg.mp hn

end Problem367.IsingObservationInnovation

end

end OAI
