import OAI.Probability.SLE.Loewner.InitialForwardKernel
import OAI.Probability.SLE.Loewner.CapacityForwardDerivative

namespace OAI

/-! The exact capacity difference quotient tends to the Loewner
kernel as the future slit shrinks to its driving point. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

theorem initialForward_quotient_tendsto (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s T : unitInterval} (hsT : s<T) (hT : T<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    Tendsto (fun t : unitInterval =>
      (initialForwardChart p hi h0 hH t z-initialForwardChart p hi h0 hH s z)/
        ((initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s:ℝ):ℂ))
      (𝓝[Ioc s T] s) (𝓝 (1/(initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hsT.trans hT):ℂ)))) := by
  let w := initialForwardChart p hi h0 hH s z-
    (initialDrivingValue p hi h0 hH s (hsT.trans hT):ℂ)
  have hzS : z∈upperHalfPlane \ range (initialSubarc p s) :=
    ⟨hz.1,fun hh => hz.2 (initialSubarc_range_mono p hsT.le hh)⟩
  have hwim : 0<w.im := by
    simpa only [w,sub_im,ofReal_im,sub_zero] using
      initialForwardChart_im_pos p hi h0 hH s hzS
  have hwn : 0<‖w‖ := hwim.trans_le ((le_abs_self w.im).trans (abs_im_le_norm w))
  have hw2 : 0<‖w‖^2 := sq_pos_of_pos hwn
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let R := min (‖w‖/4) (ε*‖w‖^2/20)
  have hR : 0<R := lt_min (by positivity) (by positivity)
  have hRn : 2*R≤‖w‖ := by
    have hh := min_le_left (‖w‖/4) (ε*‖w‖^2/20)
    change R≤‖w‖/4 at hh
    linarith
  have hRe : 10*R/‖w‖^2<ε := by
    have hh := min_le_right (‖w‖/4) (ε*‖w‖^2/20)
    change R≤ε*‖w‖^2/20 at hh
    apply (div_lt_iff₀ hw2).mpr
    nlinarith [mul_pos hε hw2]
  obtain ⟨δ,hδ,hsmall⟩ := centeredFutureArc_small p hi h0 hH s (hsT.trans hT) hR
  have htime : Tendsto (fun t : unitInterval => (t:ℝ)-(s:ℝ)) (𝓝[Ioc s T] s) (𝓝 0) := by
    have hcont : Continuous (fun t : unitInterval => (t:ℝ)-(s:ℝ)) :=
      continuous_subtype_val.sub continuous_const
    have hh := (hcont.tendsto s).mono_left
      (show 𝓝[Ioc s T] s≤𝓝 s from inf_le_left)
    simpa only [sub_self] using hh
  filter_upwards [self_mem_nhdsWithin,htime.eventually (gt_mem_nhds hδ)] with t ht htd
  have htt : t<1 := ht.2.trans_lt hT
  have hzt : z∈upperHalfPlane \ range (initialSubarc p t) :=
    ⟨hz.1,fun hh => hz.2 (initialSubarc_range_mono p ht.2 hh)⟩
  have hb := initialForward_quotient_kernel p hi h0 hH ht.1 htt hzt hR
    (hsmall t ht.1 htt htd) hRn
  rw [dist_eq_norm]
  exact hb.trans_lt hRe

end SLEExactGauge

end

end OAI
