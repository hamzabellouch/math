import OAI.Probability.FreeIsing.Ising.ConditionalCopyBounds
import OAI.Probability.FreeIsing.Ising.ObservationFactor

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable [IsProbabilityMeasure μ]

theorem kernel_graphLaw :
    ((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ =
      IsingConditionalCopyBounds.graphLaw beta μ :=
  ObservableDisintegration.compProd_kernel (observationLaw μ)
    (measurable_innovationMap beta)

theorem integrable_field_difference_sq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (t : ℝ≥0) :
    Integrable (fun p => (field beta v t p.2.1 - field beta v t p.2.2) ^ 2)
      (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_innovationMap beta).aemeasurable).mpr inferInstance
  exact (IsingConditionalCopyBounds.fieldDifference_secondMoment_bounds
    hμ hbeta kernel_graphLaw t v).1.integrable_sq

theorem initial_field_difference_energy (v : TreeVertex d) :
    (∫ p, (field beta v 0 p.2.1 - field beta v 0 p.2.2) ^ 2 ∂copies beta μ) = 0 := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_innovationMap beta).aemeasurable).mpr inferInstance
  exact IsingConditionalCopyBounds.initial_fieldDifference_secondMoment_zero
    kernel_graphLaw v

theorem isFactorOfIID_of_root_field_variance_zero
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o : TreeVertex d)
    (hzero : ∀ t, (∫ p, (field beta o t p.2.1 - field beta o t p.2.2) ^ 2
      ∂copies beta μ) = 0) :
    IsFactorOfIID d (Real.tanh beta) :=
  isFactorOfIID_of_root_field_zero hμ hbeta o
    (integrable_field_difference_sq hμ hbeta o) hzero

end Problem367.IsingObservationFactor

end

end OAI
