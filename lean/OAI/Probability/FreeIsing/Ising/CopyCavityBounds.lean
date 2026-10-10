import OAI.Probability.FreeIsing.Cavity.ArraySmallLogLoss
import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Ising.CopyStationarity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyStationarity

open IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem integrable_fieldDifference_sq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    Integrable (fun q => (IsingConditionalCopyBounds.fieldDifference beta v t q) ^ 2)
      (copies beta μ) := by
  exact (IsingConditionalCopyBounds.fieldDifference_secondMoment_bounds hμ hbeta
    (ObservableDisintegration.compProd_kernel (observationLaw μ)
      (measurable_innovationMap beta)) t v).1.integrable_sq

theorem integrable_sitePair_sub_sq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    Integrable (fun p : CavityArray.SitePair d => (p.1 v - p.2 v) ^ 2)
      ((copies beta μ).map (sitePair beta t)) := by
  have hm : Measurable (fun p : CavityArray.SitePair d => (p.1 v - p.2 v) ^ 2) :=
    (((measurable_pi_apply v).comp measurable_fst).sub
      ((measurable_pi_apply v).comp measurable_snd)).pow_const 2
  exact (integrable_map_measure hm.aestronglyMeasurable
    (measurable_sitePair beta t).aemeasurable).mpr
      (integrable_fieldDifference_sq hμ hbeta t v)

theorem integral_sitePair_cavity_sub_sq_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (o v w : TreeVertex d) :
    let h0 := tanh_nonneg_of_beta_nonneg hbeta
    let h1 := Real.tanh_lt_one beta
    let P := (copies beta μ).map (sitePair beta t)
    (∫ p, (CavityArray.field h0 h1 p.1 v w -
      CavityArray.field h0 h1 p.2 v w) ^ 2 ∂P) ≤
        (∫ p : CavityArray.SitePair d, (p.1 o - p.2 o) ^ 2 ∂P) /
          (1 - Real.tanh beta) ^ 2 := by
  exact CavityArray.integral_field_sub_sq_le
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (measurePreserving_sitePair_relabel hμ t) o v w
    (integrable_sitePair_sub_sq hμ hbeta t o)

theorem integral_sitePair_log_cavity_sub_sq_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (o v w : TreeVertex d) :
    let h0 := tanh_nonneg_of_beta_nonneg hbeta
    let h1 := Real.tanh_lt_one beta
    let P := (copies beta μ).map (sitePair beta t)
    (∫ p, (Real.log (responseAttenuation (Real.tanh beta) (CavityArray.field h0 h1 p.1 v w)) -
      Real.log (responseAttenuation (Real.tanh beta) (CavityArray.field h0 h1 p.2 v w))) ^ 2 ∂P) ≤
        cavityLogVarianceCoefficient (Real.tanh beta) *
          (∫ p : CavityArray.SitePair d, (p.1 o - p.2 o) ^ 2 ∂P) := by
  exact CavityArray.integral_log_field_sub_sq_le
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (measurePreserving_sitePair_relabel hμ t) o v w
    (integrable_sitePair_sub_sq hμ hbeta t o)

end Problem367.IsingCopyStationarity

end

end OAI
