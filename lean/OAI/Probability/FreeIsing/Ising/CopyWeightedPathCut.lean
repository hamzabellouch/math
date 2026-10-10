import OAI.Probability.FreeIsing.Ising.CopyPathBounds
import OAI.Probability.FreeIsing.Ising.CopyWeightedCut

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyWeightedPathCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open IsingCopyPathBounds IsingCopyWeightedCut

theorem integral_pathLogDifference_sq_mul_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) {ι : Type*}
    (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d) (left : Bool) (n : ℕ)
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
    (∫ q, pathLogDifference hbeta t s e q ^ 2 * g (observationCopy left q)
      ∂copies beta μ) ≤
      (C * τ) * (∫ q, pathLogDifference hbeta t s e q ^ 2 ∂copies beta μ) +
        ((s.card : ℝ) ^ 2 * edgeLogBound d beta T ^ 2) *
          Real.exp (-(I.card : ℝ) * τ ^ 2 / 2) := by
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  have hObs : HasLaw uniformObservation (observationLaw μ) (μ.prod (labelMeasure d)) :=
    ⟨measurable_uniformObservation.aemeasurable, rfl⟩
  have hLaw := ((measurePreserving_observationCopy (beta := beta) (μ := μ) left).hasLaw.identDistrib
    hObs).comp hg
  exact ActualCutWeightedAverage.integral_mul_le hμ
    (by linarith [tanh_nonneg_of_beta_nonneg hbeta]) (Real.tanh_lt_one beta).le
    n (fun _ => uniform01) F hF hbound I hI hτ hC
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmean hLaw
    (integrable_pathLogDifference_sq hμ hbeta t s e)
    (hg.comp (measurable_observationCopy left))
    (Filter.Eventually.of_forall (fun q => sq_nonneg _))
    (ae_pathLogDifference_sq_bound hμ hbeta ht s e)
    (Filter.Eventually.of_forall (fun q => (hg01 _).1))
    (Filter.Eventually.of_forall (fun q => (hg01 _).2)) hdom

end Problem367.IsingCopyWeightedPathCut

end

end OAI
