import OAI.Probability.SLE.Loewner.RawConstantTailInverse
import OAI.Probability.SLE.Loewner.SmoothRawTraceInterior
import OAI.Probability.SLE.Loewner.SmoothRawTrace

namespace OAI

/-! A constant driving tail produces the vertical slit transported by
the inverse chart at its starting time. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem trace_constant_tail (b : Driver) (A S : ℝ≥0) (hS : 0<S) (u : ℝ)
    (hb : ∀ t : ℝ≥0, A ≤ t → b t=u) :
    trace 1 b (A+S)=inverseFlow 1 b A ((u:ℂ)+trace 1 (linearDriver 0) S) := by
  have hd : ∀ t∈Icc 0 (S:ℝ), HasDerivWithinAt (driverValue (linearDriver 0)) 0
      (Icc 0 (S:ℝ)) t := fun t ht => (linearDriver_derivative 0 t ht.1).mono Icc_subset_Ici_self
  have hlim := tendsto_inverseFlow_smooth_trace (linearDriver 0) S (fun _ => 0) hd
    (show (0:ℝ) ≤ 0 from le_rfl) (fun _ _ => by simp)
  have hpos : trace 1 (linearDriver 0) S∈upperHalfPlane :=
    smooth_raw_trace_mem_upperHalfPlane (linearDriver 0) S hS (fun _ => 0) hd
      (show (0:ℝ) ≤ 0 from le_rfl) (fun _ _ => by simp)
  have hq : (u:ℂ)+trace 1 (linearDriver 0) S∈upperHalfPlane := by
    change 0<((u:ℂ)+trace 1 (linearDriver 0) S).im
    simpa only [add_im,ofReal_im,zero_add] using
      (show 0<(trace 1 (linearDriver 0) S).im from hpos)
  have hF : ContinuousAt (inverseFlow 1 b A) ((u:ℂ)+trace 1 (linearDriver 0) S) :=
    (continuousOn_inverseFlow 1 (by norm_num) b A).continuousAt (isOpen_upperHalfPlane.mem_nhds hq)
  have hright := hF.tendsto.comp (tendsto_const_nhds.add hlim)
  have hleft : Tendsto (fun y : ℝ => inverseFlow 1 b (A+S) ((u:ℂ)+(y:ℂ)*I))
      (𝓝[>] (0:ℝ)) (𝓝 (inverseFlow 1 b A ((u:ℂ)+trace 1 (linearDriver 0) S))) := by
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hw : (u:ℂ)+(y:ℂ)*I∈upperHalfPlane := by simpa [upperHalfPlane] using hy
    rw [inverseFlow_constant_tail b A S u hb hw]
    simp only [linearDriver_apply,zero_mul,ofReal_zero,zero_add,add_sub_cancel_left,Function.comp_def]
  have he : b (A+S)=u := hb _ (le_add_of_nonneg_right zero_le)
  simpa only [trace,one_mul,driverValue,←NNReal.coe_add,Real.toNNReal_coe,he] using hleft.limUnder_eq

end SLEExactGauge.Target

end

end OAI
