import OAI.Probability.FreeIsing.Ising.CopyObservables
import OAI.Probability.FreeIsing.Ising.ObservationComparison

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySmallLogLoss

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open IsingCopySpectral

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def siteVariance (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (o : TreeVertex d) (t : ℝ≥0) : ℝ :=
  ∫ q, (IsingConditionalCopyBounds.fieldDifference beta o t q) ^ 2 ∂copies beta μ

def logVariance (hbeta : 0 ≤ beta) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (v w : TreeVertex d) (t : ℝ≥0) : ℝ :=
  ∫ q, (cavityLogObservable hbeta t v w q.2.1 -
    cavityLogObservable hbeta t v w q.2.2) ^ 2 ∂copies beta μ

theorem siteVariance_nonneg (o : TreeVertex d) (t : ℝ≥0) :
    0 ≤ siteVariance beta μ o t := integral_nonneg fun _ => sq_nonneg _

theorem logVariance_nonneg (hbeta : 0 ≤ beta) (v w : TreeVertex d) (t : ℝ≥0) :
    0 ≤ logVariance hbeta μ v w t := integral_nonneg fun _ => sq_nonneg _

theorem observable_identDistrib_copies {f : Paths d → ℝ} (hf : Measurable f) :
    IdentDistrib (fun q : Paths d × (Paths d × Paths d) => f q.2.1) f
      (copies beta μ) (observationLaw μ) ∧
    IdentDistrib (fun q : Paths d × (Paths d × Paths d) => f q.2.2) f
      (copies beta μ) (observationLaw μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  constructor
  · refine ⟨(hf.comp hl.measurable).aemeasurable, hf.aemeasurable, ?_⟩
    change (copies beta μ).map (f ∘ (fun q => q.2.1)) = _
    rw [← Measure.map_map hf hl.measurable, hl.map_eq]
  · refine ⟨(hf.comp hr.measurable).aemeasurable, hf.aemeasurable, ?_⟩
    change (copies beta μ).map (f ∘ (fun q => q.2.2)) = _
    rw [← Measure.map_map hf hr.measurable, hr.map_eq]

theorem logVariance_le_siteVariance
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o v w : TreeVertex d) (t : ℝ≥0) :
    logVariance hbeta μ v w t ≤ cavityLogVarianceCoefficient (Real.tanh beta) *
      siteVariance beta μ o t := by
  have h := norm_cavityLogDifference_sq_le hμ hbeta t o v w
  rw [norm_observableDifference_sq] at h
  exact h

theorem ae_site_difference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (htT : t ≤ T) :
    ∀ᵐ q ∂copies beta μ, ∀ v : TreeVertex d,
      |field beta v t q.2.1 - field beta v t q.2.2| ≤
        2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  apply ae_all_iff.mpr
  intro v
  filter_upwards [IsingConditionalCopyBounds.ae_fieldDifference_bound hμ hbeta
    (kernel_graphLaw (beta := beta) (μ := μ)) t v] with q hq
  exact hq.trans (by exact_mod_cast (show
    2 * (t : ℝ) + 2 * (d : ℝ) * beta ≤
      2 * (T : ℝ) + 2 * (d : ℝ) * beta from by
        have h : (t : ℝ) ≤ T := htT
        linarith))

theorem logVariance_small_time_of_tail
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o v w : TreeVertex d) {t T : ℝ≥0} (ht : 0 < (t : ℝ)) (htT : t ≤ T)
    {c : ℝ}
    (hTail : observationLaw μ {x | (t : ℝ) ^ (1 / 8 : ℝ) <
      |cavityObservable hbeta t v w x|} ≤
      ENNReal.ofReal (Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2))) :
    logVariance hbeta μ v w t ≤
      cavityLogVarianceCoefficient (Real.tanh beta) * (t : ℝ) ^ (1 / 4 : ℝ) *
        siteVariance beta μ o t +
      min (cavityLogVarianceCoefficient (Real.tanh beta) * siteVariance beta μ o t)
        (cavityLogTailCoefficient (Real.tanh beta)
          (2 * (T : ℝ) + 2 * (d : ℝ) * beta) *
            Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2)) := by
  obtain ⟨hl, hr⟩ := observable_identDistrib_copies (beta := beta) (μ := μ)
    (measurable_cavityObservable hbeta t v w)
  apply integral_cavity_log_discrepancy_small_time_of_common_law
    (μ := copies beta μ) (ν := observationLaw μ)
    (Z := cavityObservable hbeta t v w)
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    ((measurable_cavityObservable hbeta t v w).comp
      (measurable_fst.comp measurable_snd))
    ((measurable_cavityObservable hbeta t v w).comp
      (measurable_snd.comp measurable_snd))
    (integrable_field_difference_sq hμ hbeta v t)
    (integrable_field_difference_sq hμ hbeta w t)
    (Y := fun q => cavityObservable hbeta t w v q.2.1)
    (Y' := fun q => cavityObservable hbeta t w v q.2.2)
  · exact Filter.Eventually.of_forall fun q =>
      ⟨CavityArray.field_spec (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
          (fun i => field beta i t q.2.1) v w,
        CavityArray.field_spec (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
          (fun i => field beta i t q.2.1) w v,
        CavityArray.field_spec (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
          (fun i => field beta i t q.2.2) v w,
        CavityArray.field_spec (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
          (fun i => field beta i t q.2.2) w v⟩
  · positivity
  · exact ht
  · filter_upwards [ae_site_difference_bound hμ hbeta htT] with q hq
    exact ⟨hq v, hq w⟩
  · exact (integral_fieldDifference_sq_eq hμ t v o).le
  · exact (integral_fieldDifference_sq_eq hμ t w o).le
  · exact hl
  · exact hr
  · exact hTail

end Problem367.IsingCopySmallLogLoss

end

end OAI
