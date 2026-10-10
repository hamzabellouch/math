import OAI.Probability.FreeIsing.Energy.ActualCriticalFieldMoments
import OAI.Probability.FreeIsing.Ising.CavityTailTransport

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCriticalSmallLogLoss

open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss
open IsingCavityTailTransport IsingCopySpectral

def varianceScale (d : ℕ) (beta : ℝ) (T : ℝ≥0) : ℝ :=
  1 + (2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2

theorem one_le_varianceScale (d : ℕ) (beta : ℝ) (T : ℝ≥0) :
    1 ≤ varianceScale d beta T := by
  unfold varianceScale
  linarith [sq_nonneg (2 * (T : ℝ) + 2 * (d : ℝ) * beta)]

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem siteVariance_zero (o : TreeVertex d) : siteVariance beta μ o 0 = 0 :=
  initial_field_difference_energy o

theorem siteVariance_le_varianceScale
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o : TreeVertex d) {t T : ℝ≥0} (htT : t ≤ T) :
    siteVariance beta μ o t ≤ varianceScale d beta T := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  have h := (IsingConditionalCopyBounds.fieldDifference_secondMoment_bounds
    hμ hbeta kernel_graphLaw t o).2.2
  have htime : (t : ℝ) ≤ T := htT
  have hb : 2 * (t : ℝ) + 2 * (d : ℝ) * beta ≤
      2 * (T : ℝ) + 2 * (d : ℝ) * beta := by linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta)
    (by positivity : 0 ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta)).2 hb
  exact h.trans (hsq.trans (by unfold varianceScale; linarith))

theorem exists_cavityObservable_critical_tail
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (ν : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure ν],
      HasFreeIsingLaw (Real.tanh beta) ν →
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → (t : ℝ) ≤ δ →
      ∀ (v w : TreeVertex d), treeAdj v w →
      observationLaw ν {x | (t : ℝ) ^ (1 / 8 : ℝ) <
        |cavityObservable hbeta t v w x|} ≤
        ENNReal.ofReal (Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2)) := by
  obtain ⟨K, hK, hMom⟩ := exists_gaussianComponentField_critical_moment_tail
    hd hbeta hcritical
  have hδ : Real.exp (-32 * K) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  refine ⟨1 / (512 * K), Real.exp (-32 * K), by positivity,
    Real.exp_pos _, hδ, ?_⟩
  intro ν _ hν t ht htδ v w hvw
  have ht1 : (t : ℝ) ≤ 1 := htδ.trans hδ.le
  have hlog : 32 * K ≤ Real.log (1 / (t : ℝ)) := by
    have h := (Real.log_le_iff_le_exp ht).2 htδ
    rw [one_div, Real.log_inv]
    linarith
  apply cavityObservable_tail_le_of_component_tails hν hbeta t hvw
  intro i
  have htail := (hMom ν hν t (show 0 < t from ht) ht1 i).2.2 hlog
  have he : -(1 / (512 * K)) * (Real.log (1 / (t : ℝ))) ^ 2 =
      -(Real.log (1 / (t : ℝ)) ^ 2) / (512 * K) := by ring
  simpa only [selectedGaussianField, RootedBroadcast.branchRoot, he] using htail

theorem exists_critical_small_log_bounds
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (ν : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure ν],
      HasFreeIsingLaw (Real.tanh beta) ν →
      ∀ (T : ℝ≥0) (o v w : TreeVertex d), treeAdj v w →
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → t ≤ T → (t : ℝ) ≤ δ →
      (logVariance hbeta ν v w t ≤
        cavityLogVarianceCoefficient (Real.tanh beta) * (t : ℝ) ^ (1 / 4 : ℝ) *
          siteVariance beta ν o t +
        min (cavityLogVarianceCoefficient (Real.tanh beta) * siteVariance beta ν o t)
          (cavityLogTailCoefficient (Real.tanh beta)
            (2 * (T : ℝ) + 2 * (d : ℝ) * beta) *
              Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2))) ∧
      (0 < siteVariance beta ν o t →
        logVariance hbeta ν v w t ≤
          (cavityLogVarianceCoefficient (Real.tanh beta) +
            2 * (cavityLogVarianceCoefficient (Real.tanh beta) +
              cavityLogTailCoefficient (Real.tanh beta)
                (2 * (T : ℝ) + 2 * (d : ℝ) * beta)) / c) *
            siteVariance beta ν o t *
            ((t : ℝ) ^ (1 / 4 : ℝ) +
              (1 + Real.log (varianceScale d beta T / siteVariance beta ν o t)) /
                (Real.log (1 / (t : ℝ))) ^ 2)) := by
  obtain ⟨c, δ, hc, hδ, hδ1, hTail⟩ :=
    exists_cavityObservable_critical_tail hd hbeta hcritical
  refine ⟨c, δ, hc, hδ, hδ1, ?_⟩
  intro ν _ hν T o v w hvw t ht htT htδ
  have hsmall := logVariance_small_time_of_tail hν hbeta o v w ht htT
    (hTail ν hν t ht htδ v w hvw)
  refine ⟨hsmall, fun hV => ?_⟩
  exact small_time_log_loss_of_minimum
    (cavityLogVarianceCoefficient_nonneg _) (cavityLogTailCoefficient_nonneg _ _)
    hc (one_le_varianceScale d beta T) hV
    (siteVariance_le_varianceScale hν hbeta o htT) ht (htδ.trans_lt hδ1) hsmall

end Problem367.IsingCriticalSmallLogLoss

end

end OAI
