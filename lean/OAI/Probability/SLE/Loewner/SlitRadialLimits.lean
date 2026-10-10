import OAI.Probability.SLE.Loewner.SlitExtendedTrace

namespace OAI

/-! Radial inverse limits for the entire extended slit, including the
joining time and every time in its constant-driver tail. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge

theorem Target.inverseFlow_radial_constant_tail (b : Driver) (A S : ℝ≥0)
    (hS : 0<S) (u : ℝ) (hb : ∀ t : ℝ≥0, A ≤ t → b t=u) :
    Tendsto (fun y : ℝ => inverseFlow 1 b (A+S) ((b (A+S):ℂ)+(y:ℂ)*I))
      (𝓝[>] (0:ℝ)) (𝓝 (trace 1 b (A+S))) := by
  have hd : ∀ t∈Icc 0 (S:ℝ), HasDerivWithinAt (driverValue (linearDriver 0)) 0
      (Icc 0 (S:ℝ)) t := fun t ht => (linearDriver_derivative 0 t ht.1).mono Icc_subset_Ici_self
  have hl := tendsto_inverseFlow_smooth_trace (linearDriver 0) S (fun _ => 0) hd
    (show (0:ℝ) ≤ 0 from le_rfl) (fun _ _ => by simp)
  have hpos := smooth_raw_trace_mem_upperHalfPlane (linearDriver 0) S hS (fun _ => 0) hd
    (show (0:ℝ) ≤ 0 from le_rfl) (fun _ _ => by simp)
  have hq : (u:ℂ)+trace 1 (linearDriver 0) S∈upperHalfPlane := by
    simpa only [upperHalfPlane,mem_ofPred_eq,add_im,ofReal_im,zero_add] using hpos
  have hc := (continuousOn_inverseFlow 1 (by norm_num) b A).continuousAt
    (isOpen_upperHalfPlane.mem_nhds hq)
  rw [trace_constant_tail b A S hS u hb]
  apply (hc.tendsto.comp (tendsto_const_nhds.add hl)).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have he := hb (A+S) (le_add_of_nonneg_right zero_le)
  have hw : (u:ℂ)+(y:ℂ)*I∈upperHalfPlane := by simpa [upperHalfPlane] using hy
  rw [he,inverseFlow_constant_tail b A S u hb hw]
  simp only [linearDriver_apply,zero_mul,ofReal_zero,zero_add,add_sub_cancel_left,Function.comp_def]

theorem slitCapacity_radial_limit (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) (t : ℝ≥0) :
    Tendsto (fun y : ℝ => Target.inverseFlow 1 (slitCapacityDriver p hi h0 hH hT) t
      ((slitCapacityDriver p hi h0 hH hT t:ℂ)+(y:ℂ)*I)) (𝓝[>] (0:ℝ))
      (𝓝 (Target.trace 1 (slitCapacityDriver p hi h0 hH hT) t)) := by
  let A := slitCapacityHorizon p hi h0 hH T
  by_cases ht : t ≤ A
  · rw [slitCapacity_raw_trace_eq p hi h0 hH hT ht]
    have hl := initialInverse_radial_driver_limit p hi h0 hH
      ((slitCapacityTime_le p hi h0 hH T t).trans_lt hT)
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [slitCapacityInverse_eq_raw p hi h0 hH hT ht (by simpa [upperHalfPlane] using hy)]
    rfl
  · have hAt : A<t := lt_of_not_ge ht
    have hh := Target.inverseFlow_radial_constant_tail (slitCapacityDriver p hi h0 hH hT)
      A (t-A) (tsub_pos_iff_lt.mpr hAt) (initialDrivingValue p hi h0 hH T hT)
      (fun s hs => slitCapacityDriver_after p hi h0 hH hT hs)
    simpa only [←NNReal.coe_add,add_tsub_cancel_of_le hAt.le] using hh

end SLEExactGauge

end

end OAI
