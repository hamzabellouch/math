import OAI.Probability.FreeIsing.Gaussian.SiteInformation
import OAI.Probability.FreeIsing.Ising.CopyInformationBound
import OAI.Probability.FreeIsing.Ising.ObservationComparison

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

def criticalCopyVarianceConstant (d : ℕ) (beta : ℝ) : ℝ :=
  (2 * (8 + 4 * (2 + 2 * (d : ℝ) * beta) ^ 2)) *
    ((1 + Real.tanh beta ^ 2) *
      Real.sqrt (1 / ((1 - Real.tanh beta ^ 2) * Real.tanh beta ^ 4)))

theorem criticalCopyVarianceConstant_nonneg (d : ℕ) (beta : ℝ) :
    0 ≤ criticalCopyVarianceConstant d beta := by
  unfold criticalCopyVarianceConstant
  positivity

namespace IsingConditionalCopyBounds

open IsingObservationInnovation

theorem posteriorInformation_critical_upper
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : TreeVertex d) :
    posteriorInformation beta μ v t ≤
      ((1 + Real.tanh beta ^ 2) *
        Real.sqrt (1 / ((1 - Real.tanh beta ^ 2) * Real.tanh beta ^ 4))) *
          Real.sqrt (t : ℝ) := by
  rw [posteriorInformation_eq_gaussian hμ t v]
  exact hμ.gaussian_site_critical_information_upper hd hbeta hcritical t ht v

theorem fieldDifference_secondMoment_critical_upper
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
    {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : TreeVertex d) :
    (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ≤
      criticalCopyVarianceConstant d beta * Real.sqrt (t : ℝ) := by
  have ht' : t ≤ (1 : ℝ≥0) := ht
  have h := fieldDifference_secondMoment_le_horizon_information
    hμ hbeta hjoint ht' v
  norm_num only [NNReal.coe_one, mul_one] at h
  apply h.trans
  calc
    _ ≤ (2 * (8 + 4 * (2 + 2 * (d : ℝ) * beta) ^ 2)) *
        (((1 + Real.tanh beta ^ 2) *
          Real.sqrt (1 / ((1 - Real.tanh beta ^ 2) * Real.tanh beta ^ 4))) *
            Real.sqrt (t : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (posteriorInformation_critical_upper hd hμ hbeta hcritical t ht v) (by positivity)
    _ = _ := by unfold criticalCopyVarianceConstant; ring

end IsingConditionalCopyBounds

namespace IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable [IsProbabilityMeasure μ]

theorem field_variance_critical_upper
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : TreeVertex d) :
    (∫ q, (field beta v t q.2.1 - field beta v t q.2.2) ^ 2 ∂copies beta μ) ≤
      criticalCopyVarianceConstant d beta * Real.sqrt (t : ℝ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  exact IsingConditionalCopyBounds.fieldDifference_secondMoment_critical_upper
    hd hμ hbeta hcritical kernel_graphLaw t ht v

theorem field_variance_critical_tendsto_zero
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (v : TreeVertex d) :
    Tendsto (fun t : ℝ≥0 =>
      ∫ q, (field beta v t q.2.1 - field beta v t q.2.2) ^ 2 ∂copies beta μ)
      (𝓝 0) (𝓝 0) := by
  have hlim : Tendsto
      (fun t : ℝ≥0 => criticalCopyVarianceConstant d beta * Real.sqrt (t : ℝ))
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous
        (fun t : ℝ≥0 => criticalCopyVarianceConstant d beta * Real.sqrt (t : ℝ)) := by
      fun_prop
    simpa only [NNReal.coe_zero, Real.sqrt_zero, mul_zero] using hc.tendsto (0 : ℝ≥0)
  apply squeeze_zero'
    (Eventually.of_forall fun t => integral_nonneg fun q => sq_nonneg _) _ hlim
  have ht : ∀ᶠ t : ℝ≥0 in 𝓝 0, (t : ℝ) < 1 :=
    (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).eventually
      (eventually_lt_nhds (by norm_num))
  exact ht.mono fun t ht => field_variance_critical_upper hd hμ hbeta hcritical t ht.le v

theorem field_variance_critical_continuousAt_zero
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (v : TreeVertex d) :
    ContinuousAt (fun t : ℝ≥0 =>
      ∫ q, (field beta v t q.2.1 - field beta v t q.2.2) ^ 2 ∂copies beta μ) 0 := by
  change Tendsto _ (𝓝 0) (𝓝 _)
  dsimp only
  rw [initial_field_difference_energy v]
  exact field_variance_critical_tendsto_zero hd hμ hbeta hcritical v

theorem field_variance_critical_real_tendsto_zero
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (v : TreeVertex d) :
    Tendsto (fun t : ℝ =>
      ∫ q, (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) ^ 2
        ∂copies beta μ) (𝓝 0) (𝓝 0) := by
  exact (field_variance_critical_tendsto_zero hd hμ hbeta hcritical v).comp
    (by simpa using continuous_real_toNNReal.tendsto (0 : ℝ))

end IsingObservationFactor

end Problem367

end

end OAI
