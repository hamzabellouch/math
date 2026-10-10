import OAI.Probability.SLE.Loewner.SlitReflectedInterior

namespace OAI

/-! The uniformly separated boundary coordinates admit passage through
the exact interior Loewner integral. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology NNReal

namespace SLEExactGauge

lemma slitReflectedFlow_real_kernel_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {x : ℝ} (hx : x≠0) :
    Continuous (fun t : ℝ => 2/(slitReflectedFlow p hi h0 hH T (x:ℂ) t-
      (slitCapacityDriver p hi h0 hH hT t.toNNReal:ℂ))) :=
  continuous_const.div ((slitReflectedFlow_real_continuous p hi h0 hH T hx).sub
    (Complex.continuous_ofReal.comp
      ((slitCapacityDriver p hi h0 hH hT).continuous.comp continuous_real_toNNReal)))
    (slitReflectedFlow_separated p hi h0 hH hT hx)

lemma slitReflectedFlow_near_real_mem (p : C(unitInterval,ℂ))
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {x : ℝ} (hx : x≠0) :
    ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), (x:ℂ)+(y:ℂ)*I∈upperHalfPlane \ range p := by
  have hD : IsOpen (range p)ᶜ := (isCompact_range p.continuous).isClosed.isOpen_compl
  have hxD : (x:ℂ)∈(range p)ᶜ := fun he => real_not_reflected_arc p h0 hH hx (Or.inl he)
  have hv : Tendsto (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have hc : Continuous (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) := by fun_prop
    simpa only [ofReal_zero,zero_mul,add_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hv.eventually (hD.mem_nhds hxD)] with y hy hyD
  exact ⟨by simpa [upperHalfPlane] using hy,hyD⟩

lemma slitReflectedFlow_near_real_kernel_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {x : ℝ} (hx : x≠0) :
    ∃ C : ℝ, ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ),
      ∀ t∈Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ),
      ‖2/(slitReflectedFlow p hi h0 hH T ((x:ℂ)+(y:ℂ)*I) t-
        (slitCapacityDriver p hi h0 hH hT t.toNNReal:ℂ))‖≤C := by
  obtain ⟨m,hm,hgap⟩ := slitReflectedFlow_positive_gap p hi h0 hH hT hx
  have hc := Metric.tendstoUniformly_iff.mp (slitReflectedFlow_uniform_limit p hi h0 hH T hx)
    (m/2) (half_pos hm)
  refine ⟨4/m,?_⟩
  filter_upwards [hc] with y hy t ht
  let q := slitReflectedFlow p hi h0 hH T ((x:ℂ)+(y:ℂ)*I) t
  let r := slitReflectedFlow p hi h0 hH T (x:ℂ) t
  let u : ℂ := (slitCapacityDriver p hi h0 hH hT t.toNNReal:ℂ)
  have hsmall : ‖r-q‖< m/2 := by simpa only [dist_eq_norm] using hy t
  have htri := norm_sub_le_norm_sub_add_norm_sub r q u
  have hlarge : m/2<‖q-u‖ := by linarith [hgap t ht]
  have hnorm : 0<‖q-u‖ := (half_pos hm).trans hlarge
  change ‖(2:ℂ)/(q-u)‖≤4/m
  rw [norm_div,Complex.norm_ofNat]
  apply (div_le_div_iff₀ hnorm hm).mpr
  nlinarith

theorem slitReflectedFlow_integral_tendsto (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {x : ℝ} (hx : x≠0)
    {t : ℝ} (ht : t∈Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ)) :
    Tendsto (fun y : ℝ => ∫ u in 0..t,
      2/(slitReflectedFlow p hi h0 hH T ((x:ℂ)+(y:ℂ)*I) u-
        (slitCapacityDriver p hi h0 hH hT u.toNNReal:ℂ))) (𝓝[>] (0:ℝ))
      (𝓝 (∫ u in 0..t, 2/(slitReflectedFlow p hi h0 hH T (x:ℂ) u-
        (slitCapacityDriver p hi h0 hH hT u.toNNReal:ℂ)))) := by
  obtain ⟨C,hC⟩ := slitReflectedFlow_near_real_kernel_bound p hi h0 hH hT hx
  have hmem := slitReflectedFlow_near_real_mem p h0 hH hx
  simp_rw [intervalIntegral.integral_of_le ht.1]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · filter_upwards [hmem] with y hy
    exact (slitReflectedFlow_interior_kernel_continuous p hi h0 hH hT hy).aestronglyMeasurable
  · filter_upwards [hC] with y hy
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
    exact hy u ⟨hu.1.le,hu.2.trans ht.2⟩
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u _hu
    exact tendsto_const_nhds.div
      (((slitReflectedFlow_uniform_limit p hi h0 hH T hx).tendsto_at u).sub_const _)
      (slitReflectedFlow_separated p hi h0 hH hT hx u)

theorem slitReflectedFlow_boundary_integral (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {x : ℝ} (hx : x≠0)
    {t : ℝ} (ht : t∈Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ)) :
    (∫ u in 0..t, 2/(slitReflectedFlow p hi h0 hH T (x:ℂ) u-
      (slitCapacityDriver p hi h0 hH hT u.toNNReal:ℂ)))=
      slitReflectedFlow p hi h0 hH T (x:ℂ) t-(x:ℂ) := by
  have hv : Tendsto (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have hc : Continuous (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) := by fun_prop
    simpa only [ofReal_zero,zero_mul,add_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique (slitReflectedFlow_integral_tendsto p hi h0 hH hT hx ht)
  apply (((slitReflectedFlow_uniform_limit p hi h0 hH T hx).tendsto_at t).sub hv).congr'
  filter_upwards [slitReflectedFlow_near_real_mem p h0 hH hx] with y hy
  exact (slitReflectedFlow_interior_integral p hi h0 hH hT hy ht).symm

end SLEExactGauge

end

end OAI
