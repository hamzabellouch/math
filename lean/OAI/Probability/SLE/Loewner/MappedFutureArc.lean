import OAI.Probability.SLE.Loewner.InitialDrivingLimit
import OAI.Probability.SLE.Loewner.FillEndpoint
import OAI.Probability.SLE.Loewner.InitialChartIdentities

namespace OAI

/-! Each finite future subarc becomes a continuous attached arc in the
current half-plane chart. Its initial value is the proved driving limit. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma initialForwardChart_continuousAt (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p s)) :
    ContinuousAt (initialForwardChart p hi h0 hH s) z := by
  by_cases hs : s=0
  · simpa only [hs,initialForwardChart_zero] using continuousAt_id (x := z)
  · rw [initialForwardChart,dite_eq_right hs]
    exact ((initialSlitChart p hi h0 hH s hs).forward_differentiable.continuousOn z hz).continuousAt
      ((initialSlitChart p hi h0 hH s hs).isOpen_domain.mem_nhds hz)

def mappedFutureRaw (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s t : unitInterval) (r : ℝ) : ℂ :=
  initialForwardChart p hi h0 hH s
    (p (slitFutureParameter s (((t:ℝ)-(s:ℝ))*r)))

lemma future_scaled_offset {s t : unitInterval} (hst : s<t) (ht : t<1)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) 1) :
    ((t:ℝ)-(s:ℝ))*r∈Ioo 0 (1-(s:ℝ)) := by
  have hd : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  refine ⟨mul_pos hd hr.1,?_⟩
  have hm := mul_le_mul_of_nonneg_left hr.2 hd.le
  have ht' : (t:ℝ)<1 := ht
  nlinarith

lemma mappedFutureRaw_continuousAt (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) {r : ℝ} (hr : r∈Ioc (0:ℝ) 1) :
    ContinuousAt (mappedFutureRaw p hi h0 hH s t) r := by
  have hz := slitFuturePoint_mem_domain p hi hH s (future_scaled_offset hst ht hr)
  have hc : Continuous (fun r : ℝ => p (slitFutureParameter s (((t:ℝ)-(s:ℝ))*r))) :=
    p.continuous.comp ((slitFutureParameter_continuous s).comp
      (continuous_const.mul continuous_id))
  change ContinuousAt (fun r : ℝ => initialForwardChart p hi h0 hH s
    (p (slitFutureParameter s (((t:ℝ)-(s:ℝ))*r)))) r
  exact (initialForwardChart_continuousAt p hi h0 hH s hz).comp
    (f := fun r : ℝ => p (slitFutureParameter s (((t:ℝ)-(s:ℝ))*r)))
    (show ContinuousAt (fun r : ℝ => p (slitFutureParameter s (((t:ℝ)-(s:ℝ))*r))) r from
      hc.continuousAt)

lemma mappedFutureRaw_tendsto (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) :
    Tendsto (mappedFutureRaw p hi h0 hH s t) (𝓝[>] (0:ℝ))
      (𝓝 ((initialDrivingValue p hi h0 hH s (hst.trans ht)):ℂ)) := by
  have hd : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hc : Tendsto (fun r : ℝ => ((t:ℝ)-(s:ℝ))*r) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hmul : Continuous (fun r : ℝ => ((t:ℝ)-(s:ℝ))*r) :=
        continuous_const.mul continuous_id
      have hh : Tendsto (fun r : ℝ => ((t:ℝ)-(s:ℝ))*r) (𝓝 (0:ℝ)) (𝓝 0) := by
        simpa only [mul_zero] using hmul.tendsto 0
      exact hh.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hd hr
  exact (initialDrivingValue_spec p hi h0 hH s (hst.trans ht)).comp hc

noncomputable def mappedFutureArc (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) : C(unitInterval,ℂ) where
  toFun u := if (u:ℝ)=0 then (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)
    else mappedFutureRaw p hi h0 hH s t u
  continuous_toFun := (continuousOn_fill_endpoint
    (fun _ hr => mappedFutureRaw_continuousAt p hi h0 hH hst ht hr)
    (mappedFutureRaw_tendsto p hi h0 hH hst ht)).comp_continuous continuous_subtype_val
      (fun u => u.property)

@[simp] lemma mappedFutureArc_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) :
    mappedFutureArc p hi h0 hH hst ht 0=
      (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ) := by
  change (if (0:ℝ)=0 then _ else _)=_
  exact ite_eq_left rfl

lemma mappedFutureArc_upper (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1)
    {u : unitInterval} (hu : u≠0) :
    mappedFutureArc p hi h0 hH hst ht u∈upperHalfPlane := by
  have hp : 0<(u:ℝ) := unitInterval.pos_iff_ne_zero.mpr hu
  have hc : (u:ℝ)≠0 := ne_of_gt hp
  change (if (u:ℝ)=0 then _ else _)∈upperHalfPlane
  rw [ite_eq_right hc]
  exact initialForwardChart_mem_upper p hi h0 hH s
    (slitFuturePoint_mem_domain p hi hH s (future_scaled_offset hst ht ⟨hp,u.property.2⟩))

end SLEExactGauge

end

end OAI
