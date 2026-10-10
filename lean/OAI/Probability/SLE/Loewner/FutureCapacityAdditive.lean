import OAI.Probability.SLE.Loewner.FutureComposedCharts
import OAI.Probability.SLE.Loewner.ShiftedHydrodynamicComposition
import OAI.Probability.SLE.Loewner.SlitChartUniqueness

namespace OAI

/-! Removing an initial slit and its exact mapped future adds the two
hydrodynamic capacities. The composed chart is the later normalized
chart, including when the initial time is zero. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

variable (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
  (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
  {s t : unitInterval} (hst : s<t) (ht : t<1)

noncomputable def composedFutureSlitChart : SimpleSlitChart (initialSubarc p t) := by
  have h := future_composed_chart_properties p hi h0 hH hst ht
  have hG := h.1
  have hF := h.2.1
  have hGm := h.2.2.1
  have hFm := h.2.2.2.1
  have hl := h.2.2.2.2.1
  have hr := h.2.2.2.2.2
  let Q := futureSlitChart p hi h0 hH hst ht
  let U := initialDrivingValue p hi h0 hH s (hst.trans ht)
  refine ⟨futureComposedForward p hi h0 hH hst ht,
    futureComposedInverse p hi h0 hH hst ht,initialCapacity p hi h0 hH s+Q.capacity,
    add_pos_of_nonneg_of_pos (initialCapacity_nonneg p hi h0 hH s) Q.capacity_pos,
    ?_,hG,hF,hFm,hl,hr,?_,?_,?_⟩
  · refine ⟨hGm,?_,?_⟩
    · intro z hz w hw he
      have hh := congrArg (futureComposedInverse p hi h0 hH hst ht) he
      simpa only [hl z hz,hl w hw] using hh
    · intro w hw
      exact ⟨_,hFm hw,hr w hw⟩
  · simpa only [futureComposedForward,ofReal_add] using
      shifted_hydrodynamic_coefficient U (initialForwardChart_coefficient p hi h0 hH s) Q.coefficient
  · exact shifted_inverse_normalized U (initialInverseChart_normalized p hi h0 hH s)
      Q.inverse_normalized (fun _ hz => (Q.inverse_mapsTo hz).1)
  · intro z hz
    have hsub : z∈upperHalfPlane \ range (initialSubarc p s) :=
      ⟨hz.1,fun he => hz.2 (initialSubarc_range_mono p hst.le he)⟩
    have hd := (initialForward_centered_bijOn p hi h0 hH hst ht).mapsTo hz
    have hh := Q.height_le _ hd
    change (Q.forward (initialForwardChart p hi h0 hH s z-(U:ℂ))).im≤
      (initialForwardChart p hi h0 hH s z-(U:ℂ)).im at hh
    simp only [sub_im,ofReal_im,sub_zero] at hh
    change ((U:ℂ)+Q.forward (initialForwardChart p hi h0 hH s z-(U:ℂ))).im≤z.im
    simpa only [add_im,ofReal_im,zero_add] using
      hh.trans (initialForwardChart_height_le p hi h0 hH s hsub)

theorem futureSlitChart_capacity_eq :
    (futureSlitChart p hi h0 hH hst ht).capacity=
      initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s := by
  have ht0 : t≠0 := ne_of_gt (lt_of_le_of_lt bot_le hst)
  have hh := ((composedFutureSlitChart p hi h0 hH hst ht).unique_on_domain
    (initialSlitChart p hi h0 hH t ht0)).2.2
  change initialCapacity p hi h0 hH s+(futureSlitChart p hi h0 hH hst ht).capacity=
    (initialSlitChart p hi h0 hH t ht0).capacity at hh
  rw [initialCapacity,dite_eq_right ht0]
  linarith

theorem futureComposedForward_eq {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p t)) :
    futureComposedForward p hi h0 hH hst ht z=initialForwardChart p hi h0 hH t z := by
  have ht0 : t≠0 := ne_of_gt (lt_of_le_of_lt bot_le hst)
  have hh := ((composedFutureSlitChart p hi h0 hH hst ht).unique_on_domain
    (initialSlitChart p hi h0 hH t ht0)).1 hz
  simpa only [composedFutureSlitChart,initialForwardChart,dite_eq_right ht0] using hh

theorem futureComposedInverse_eq {z : ℂ} (hz : z∈upperHalfPlane) :
    futureComposedInverse p hi h0 hH hst ht z=initialInverseChart p hi h0 hH t z := by
  have ht0 : t≠0 := ne_of_gt (lt_of_le_of_lt bot_le hst)
  have hh := ((composedFutureSlitChart p hi h0 hH hst ht).unique_on_domain
    (initialSlitChart p hi h0 hH t ht0)).2.1 hz
  simpa only [composedFutureSlitChart,initialInverseChart,dite_eq_right ht0] using hh

end SLEExactGauge

end

end OAI
