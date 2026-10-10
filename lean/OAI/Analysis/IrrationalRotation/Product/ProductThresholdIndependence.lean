import OAI.Analysis.IrrationalRotation.Couplings.ConditionalDistributionEvents
import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalKernels

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace Invariant233.OrderedProductCoupling

theorem right_thresholds_iCondIndepSet_via_events (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet (MeasurableSpace.comap leftEndpoint inferInstance)
      leftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ rightEndpoint ω i}) (law P) := by
  exact ConditionalDistributionEvents.iCondIndepSet_coordinate_preimage_of_condDistrib
    (law P) leftEndpoint rightEndpoint leftEndpoint_measurable rightEndpoint_measurable
    (fun i (y : Endpoint) => y i) (fun i => measurable_pi_apply i)
    (fun i => Ici (u i)) (fun _ => measurableSet_Ici)
    (right_coordinates_conditionally_independent P)

theorem left_thresholds_iCondIndepSet_via_events (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet (MeasurableSpace.comap rightEndpoint inferInstance)
      rightEndpoint_measurable.comap_le
      (fun i => {ω : Sample | leftEndpoint ω i < u i}) (law P) := by
  exact ConditionalDistributionEvents.iCondIndepSet_coordinate_preimage_of_condDistrib
    (law P) rightEndpoint leftEndpoint rightEndpoint_measurable leftEndpoint_measurable
    (fun i (x : Endpoint) => x i) (fun i => measurable_pi_apply i)
    (fun i => Iio (u i)) (fun _ => measurableSet_Iio)
    (left_coordinates_conditionally_independent P)

end Invariant233.OrderedProductCoupling

end

end OAI
