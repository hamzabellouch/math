import OAI.Probability.FreeIsing.Ising.CopyCavityBounds
import OAI.Probability.FreeIsing.Ising.ObservationComparison
import OAI.Probability.FreeIsing.Trees.ActualCutWeightedAverage

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyWeightedCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds

def observationCopy {d : ℕ} (left : Bool) (q : CopySpace d) : Paths d :=
  if left then q.2.1 else q.2.2

theorem measurable_observationCopy {d : ℕ} (left : Bool) :
    Measurable (observationCopy (d := d) left) := by
  cases left
  · exact measurable_snd.comp measurable_snd
  · exact measurable_fst.comp measurable_snd

theorem measurePreserving_observationCopy {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ] (left : Bool) :
    MeasurePreserving (observationCopy left) (copies beta μ) (observationLaw μ) := by
  obtain ⟨hl, hr⟩ := IsingCopyStationarity.measurePreserving_observations
    (beta := beta) (μ := μ)
  cases left
  · exact hr
  · exact hl

theorem integral_fieldDifference_sq_mul_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o : TreeVertex d) (t : ℝ≥0) (left : Bool) (n : ℕ)
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → ℝ) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d n)) (hI : I.Nonempty) {τ C : ℝ}
    (hτ : 0 ≤ τ) (hC : 0 ≤ C)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (labelMeasure d)) ≤ τ / 4)
    (g : Paths d → ℝ) (hg : Measurable g) (hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hdom : ∀ᵐ z ∂μ.prod (labelMeasure d),
      g (uniformObservation z) ≤ C * ActualCutWeightedAverage.average F I z) :
    (∫ q, (fieldDifference beta o t q) ^ 2 * g (observationCopy left q) ∂copies beta μ) ≤
      (C * τ) * (∫ q, (fieldDifference beta o t q) ^ 2 ∂copies beta μ) +
        (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
          Real.exp (-(I.card : ℝ) * τ ^ 2 / 2) := by
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  let : IsProbabilityMeasure (observationLaw μ) := inferInstance
  let : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  let : IsProbabilityMeasure (copies beta μ) := by unfold copies; infer_instance
  have hObs : HasLaw uniformObservation (observationLaw μ) (μ.prod (labelMeasure d)) :=
    ⟨measurable_uniformObservation.aemeasurable, rfl⟩
  have hLaw := ((measurePreserving_observationCopy (beta := beta) (μ := μ) left).hasLaw.identDistrib
    hObs).comp hg
  have hweight := IsingCopyStationarity.integrable_fieldDifference_sq hμ hbeta t o
  have hmax : ∀ᵐ q ∂copies beta μ, (fieldDifference beta o t q) ^ 2 ≤
      (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
    filter_upwards [ae_fieldDifference_bound hμ hbeta kernel_graphLaw t o] with q hq
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hq 2
  exact ActualCutWeightedAverage.integral_mul_le hμ
    (by linarith [tanh_nonneg_of_beta_nonneg hbeta]) (Real.tanh_lt_one beta).le
    n (fun _ => uniform01) F hF hbound I hI hτ hC (sq_nonneg _) hmean
    hLaw hweight (hg.comp (measurable_observationCopy left))
    (Filter.Eventually.of_forall (fun q => sq_nonneg _)) hmax
    (Filter.Eventually.of_forall (fun q => (hg01 _).1))
    (Filter.Eventually.of_forall (fun q => (hg01 _).2)) hdom

end Problem367.IsingCopyWeightedCut

end

end OAI
