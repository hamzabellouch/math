import OAI.Analysis.IrrationalRotation.Analysis.ObservationConditioning
import OAI.Analysis.IrrationalRotation.Couplings.ProductCouplingCircle

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Invariant233.OrderedProductCoupling

theorem left_condExp_eq_circle (P : Parameters) (f : Sample → ℝ) :
    (law P)[f | (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]
      =ᵐ[law P]
    (law P)[f | (inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint] := by
  apply ObservationConditioning.condExp_comap_of_ae_section (law P)
    leftEndpoint_measurable circleLeftEndpoint_measurable
    realEndpoint_measurable circleEndpoint_measurable circleEndpoint_realEndpoint
  exact (ae_real_circle_endpoints P).mono (fun _ h => h.1)

theorem right_condExp_eq_circle (P : Parameters) (f : Sample → ℝ) :
    (law P)[f | (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]
      =ᵐ[law P]
    (law P)[f | (inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint] := by
  apply ObservationConditioning.condExp_comap_of_ae_section (law P)
    rightEndpoint_measurable circleRightEndpoint_measurable
    realEndpoint_measurable circleEndpoint_measurable circleEndpoint_realEndpoint
  exact (ae_real_circle_endpoints P).mono (fun _ h => h.2)

theorem left_iCondIndepSet_iff_circle {ι : Type*} [Countable ι]
    (P : Parameters) (events : ι → Set Sample)
    (hmeas : ∀ i, MeasurableSet (events i)) :
    iCondIndepSet ((inferInstance : MeasurableSpace Endpoint).comap leftEndpoint)
      leftEndpoint_measurable.comap_le events (law P) ↔
    iCondIndepSet ((inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint)
      circleLeftEndpoint_measurable.comap_le events (law P) := by
  apply ObservationConditioning.iCondIndepSet_comap_iff_of_ae_section (law P)
    leftEndpoint_measurable circleLeftEndpoint_measurable
    realEndpoint_measurable circleEndpoint_measurable circleEndpoint_realEndpoint
    _ events hmeas
  exact (ae_real_circle_endpoints P).mono (fun _ h => h.1)

theorem right_iCondIndepSet_iff_circle {ι : Type*} [Countable ι]
    (P : Parameters) (events : ι → Set Sample)
    (hmeas : ∀ i, MeasurableSet (events i)) :
    iCondIndepSet ((inferInstance : MeasurableSpace Endpoint).comap rightEndpoint)
      rightEndpoint_measurable.comap_le events (law P) ↔
    iCondIndepSet ((inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint)
      circleRightEndpoint_measurable.comap_le events (law P) := by
  apply ObservationConditioning.iCondIndepSet_comap_iff_of_ae_section (law P)
    rightEndpoint_measurable circleRightEndpoint_measurable
    realEndpoint_measurable circleEndpoint_measurable circleEndpoint_realEndpoint
    _ events hmeas
  exact (ae_real_circle_endpoints P).mono (fun _ h => h.2)

theorem right_threshold_event_ae_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    {ω : Sample | u i ≤ rightEndpoint ω i} =ᵐ[law P]
      {ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i} := by
  filter_upwards [ae_real_circle_endpoints P] with ω hω
  rw [hω.2]

theorem left_threshold_event_ae_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    {ω : Sample | leftEndpoint ω i < u i} =ᵐ[law P]
      {ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i} := by
  filter_upwards [ae_real_circle_endpoints P] with ω hω
  rw [hω.1]

theorem right_threshold_condExp_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    (law P)[({ω : Sample | u i ≤ rightEndpoint ω i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint] =ᵐ[law P]
    (law P)[({ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i}).indicator
      (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint] := by
  exact (left_condExp_eq_circle P _).trans
    (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set
      (right_threshold_event_ae_eq_circle P u i)))

theorem left_threshold_condExp_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    (law P)[({ω : Sample | leftEndpoint ω i < u i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint] =ᵐ[law P]
    (law P)[({ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i}).indicator
      (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint] := by
  exact (right_condExp_eq_circle P _).trans
    (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set
      (left_threshold_event_ae_eq_circle P u i)))

theorem right_threshold_iCondIndepSet_iff_circle (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet ((inferInstance : MeasurableSpace Endpoint).comap leftEndpoint)
      leftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ rightEndpoint ω i}) (law P) ↔
    iCondIndepSet ((inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint)
      circleLeftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i}) (law P) := by
  have hraw (i : ℕ) : MeasurableSet {ω : Sample | u i ≤ rightEndpoint ω i} :=
    measurableSet_le measurable_const ((measurable_pi_apply i).comp rightEndpoint_measurable)
  have hcircle (i : ℕ) :
      MeasurableSet {ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i} :=
    measurableSet_le measurable_const
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp circleRightEndpoint_measurable))
  exact (left_iCondIndepSet_iff_circle P _ hraw).trans
    (ObservationConditioning.iCondIndepSet_iff_of_events_ae_eq
      _ circleLeftEndpoint_measurable.comap_le (law P) _ _ hraw hcircle
      (right_threshold_event_ae_eq_circle P u))

theorem left_threshold_iCondIndepSet_iff_circle (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet ((inferInstance : MeasurableSpace Endpoint).comap rightEndpoint)
      rightEndpoint_measurable.comap_le
      (fun i => {ω : Sample | leftEndpoint ω i < u i}) (law P) ↔
    iCondIndepSet ((inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint)
      circleRightEndpoint_measurable.comap_le
      (fun i => {ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i}) (law P) := by
  have hraw (i : ℕ) : MeasurableSet {ω : Sample | leftEndpoint ω i < u i} :=
    measurableSet_lt ((measurable_pi_apply i).comp leftEndpoint_measurable) measurable_const
  have hcircle (i : ℕ) :
      MeasurableSet {ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i} :=
    measurableSet_lt
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp circleLeftEndpoint_measurable))
      measurable_const
  exact (right_iCondIndepSet_iff_circle P _ hraw).trans
    (ObservationConditioning.iCondIndepSet_iff_of_events_ae_eq
      _ circleRightEndpoint_measurable.comap_le (law P) _ _ hraw hcircle
      (left_threshold_event_ae_eq_circle P u))

end Invariant233.OrderedProductCoupling

end OAI
