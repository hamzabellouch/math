import OAI.Probability.FreeIsing.Brownian.IntegralProcess
import OAI.Probability.FreeIsing.Brownian.IntegralTransport
import OAI.Probability.FreeIsing.Ising.CanonicalPosteriorStops

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy BrownianIntegralProcess

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  [IsProbabilityMeasure μ]

theorem ae_innovationMap_projection (j : Bool) :
    ∀ᵐ q ∂copies beta μ, innovationMap beta (projection j q) = q.1 := by
  have h := IsingConditionalCopyBounds.ae_innovationMap_copies
    (beta := beta) (μ := μ)
    (rho := (observationLaw μ).map (innovationMap beta))
    (eta := kernel beta μ) kernel_graphLaw
  filter_upwards [h] with q hq
  cases j
  · exact hq.2
  · exact hq.1

theorem stoppedUniformSum_copy_eq_ae (j : Bool) (v : TreeVertex d)
    (H : ℝ≥0 → Paths d → ℝ) :
    ∀ᵐ q ∂copies beta μ, ∀ (T : ℝ≥0) (n : ℕ) (t : ℝ≥0),
      stoppedUniformSum (fun s (p : Joint d) => p.1 v s)
        (fun s p => H s (projection j p)) T n t q =
      stoppedUniformSum (fun s x => innovationMap beta x v s) H T n t
        (projection j q) := by
  filter_upwards [ae_innovationMap_projection (beta := beta) (μ := μ) j] with q hq
  intro T n t
  simp only [stoppedUniformSum, StoppedSimpleIntegral.intervalSum, hq]

theorem tendsto_stoppedUniformSum_copy (j : Bool) (v : TreeVertex d)
    {H I : ℝ≥0 → Paths d → ℝ}
    (hH : ∀ s, StronglyMeasurable (H s)) (T t : ℝ≥0)
    (hI : AEStronglyMeasurable (I t) (observationLaw μ))
    (hlim : Tendsto (fun n => ∫ x,
      (stoppedUniformSum (fun s x => innovationMap beta x v s) H T n t x - I t x) ^ 2
        ∂observationLaw μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ q,
      (stoppedUniformSum (fun s (p : Joint d) => p.1 v s)
        (fun s p => H s (projection j p)) T n t q - I t (projection j q)) ^ 2
          ∂copies beta μ) atTop (𝓝 0) := by
  have hB (s : ℝ≥0) : Measurable (fun x : Paths d => innovationMap beta x v s) :=
    (continuous_eval_const s).measurable.comp
      ((measurable_pi_apply v).comp (measurable_innovationMap beta))
  have hm (n : ℕ) : AEStronglyMeasurable
      (stoppedUniformSum (fun s x => innovationMap beta x v s) H T n t)
      (observationLaw μ) := by
    apply Measurable.aestronglyMeasurable
    unfold stoppedUniformSum StoppedSimpleIntegral.intervalSum
    exact Finset.measurable_sum _ (fun i _ =>
      (hH _).measurable.mul ((hB _).sub (hB _)))
  have hp := BrownianGrid.meanSquare_limit_comp
    (copyProjection_measurePreserving beta μ j) hm hI hlim
  have heq (n : ℕ) :
      (∫ q, (stoppedUniformSum (fun s (p : Joint d) => p.1 v s)
        (fun s p => H s (projection j p)) T n t q - I t (projection j q)) ^ 2
          ∂copies beta μ) =
      ∫ q, (stoppedUniformSum (fun s x => innovationMap beta x v s) H T n t
        (projection j q) - I t (projection j q)) ^ 2 ∂copies beta μ := by
    apply integral_congr_ae
    filter_upwards [stoppedUniformSum_copy_eq_ae (beta := beta) (μ := μ) j v H] with q hq
    rw [hq T n t]
  simpa only [heq] using hp

theorem integer_stoppedUniformSum_limits_copy (j : Bool) (v : TreeVertex d)
    {H I : ℝ≥0 → Paths d → ℝ}
    (hH : StronglyAdapted (filtration d) H)
    (hI : ∀ t, MemLp (I t) 2 (observationLaw μ))
    (hlim : ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (stoppedUniformSum (fun s x => innovationMap beta x v s) H N n t x - I t x) ^ 2
          ∂observationLaw μ) atTop (𝓝 0)) :
    ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ q,
        (stoppedUniformSum (fun s (p : Joint d) => p.1 v s)
          (fun s p => H s (projection j p)) N n t q - I t (projection j q)) ^ 2
            ∂copies beta μ) atTop (𝓝 0) := by
  intro N hN t ht
  exact tendsto_stoppedUniformSum_copy j v (fun s => (hH s).mono ((filtration d).le s))
    N t (hI t).aestronglyMeasurable (hlim N hN t ht)

end Problem367.IsingObservationFactor

end

end OAI
