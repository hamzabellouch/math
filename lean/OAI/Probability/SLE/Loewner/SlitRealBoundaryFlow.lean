import OAI.Probability.SLE.Geometry.ReflectedRealSeparation
import OAI.Probability.SLE.Loewner.SlitPhysicalClock

namespace OAI

/-! The exact capacity-clock real boundary coordinates are continuous,
real valued and uniformly separated from the driver on a finite prefix. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology NNReal

namespace SLEExactGauge

noncomputable def slitReflectedFlow (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (z : ℂ) (t : ℝ) : ℂ :=
  initialReflectedForward p hi h0 hH (slitCapacityTime p hi h0 hH T t.toNNReal) z

lemma slitReflectedFlow_real_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {x : ℝ} (hx : x≠0) :
    Continuous (slitReflectedFlow p hi h0 hH T (x:ℂ)) :=
  (initialReflectedForward_real_continuous p hi h0 hH hx).comp
    ((slitCapacityTime_continuous p hi h0 hH T).comp continuous_real_toNNReal)

lemma slitReflectedFlow_real (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {x : ℝ} (hx : x≠0) (t : ℝ) :
    (slitReflectedFlow p hi h0 hH T (x:ℂ) t).im=0 :=
  initialReflectedForward_real p hi h0 hH _ hx

lemma slitReflectedFlow_separated (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {x : ℝ} (hx : x≠0) (t : ℝ) :
    slitReflectedFlow p hi h0 hH T (x:ℂ) t-
      (slitCapacityDriver p hi h0 hH hT t.toNNReal:ℂ)≠0 := by
  apply sub_ne_zero.mpr
  exact initialReflectedForward_ne_driver p hi h0 hH
    ((slitCapacityTime_le p hi h0 hH T t.toNNReal).trans_lt hT) hx

theorem slitReflectedFlow_uniform_limit (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {x : ℝ} (hx : x≠0) :
    TendstoUniformly (fun y : ℝ => slitReflectedFlow p hi h0 hH T ((x:ℂ)+(y:ℂ)*I))
      (slitReflectedFlow p hi h0 hH T (x:ℂ)) (𝓝[>] (0:ℝ)) := by
  have hv : Tendsto (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have hc : Continuous (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) := by fun_prop
    simpa only [ofReal_zero,zero_mul,add_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := Metric.equicontinuousAt_iff_right.mp
    (initialReflectedForward_equicontinuousAt_real p hi h0 hH hx) ε hε
  filter_upwards [hv.eventually he] with y hy t
  exact hy (slitCapacityTime p hi h0 hH T t.toNNReal)

lemma slitReflectedFlow_positive_gap (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {x : ℝ} (hx : x≠0) :
    ∃ m : ℝ, 0 < m ∧ ∀ t∈Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ),
      m ≤ ‖slitReflectedFlow p hi h0 hH T (x:ℂ) t-
        (slitCapacityDriver p hi h0 hH hT t.toNNReal:ℂ)‖ := by
  have hc : Continuous (fun t : ℝ => ‖slitReflectedFlow p hi h0 hH T (x:ℂ) t-
      (slitCapacityDriver p hi h0 hH hT t.toNNReal:ℂ)‖) :=
    ((slitReflectedFlow_real_continuous p hi h0 hH T hx).sub
      (Complex.continuous_ofReal.comp
        ((slitCapacityDriver p hi h0 hH hT).continuous.comp continuous_real_toNNReal))).norm
  obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (slitCapacityHorizon p hi h0 hH T).coe_nonneg) hc.continuousOn
  exact ⟨_,norm_pos_iff.mpr (slitReflectedFlow_separated p hi h0 hH hT hx t),
    fun u hu => hmin hu⟩

end SLEExactGauge

end

end OAI
