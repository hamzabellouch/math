import OAI.Probability.SLE.Loewner.SmoothRawTipGlobal

namespace OAI

/-! The prescribed raw trace is the actual radial limit for smooth
drivers. A quantitative radial error bound is retained for time continuity. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem tendsto_inverseFlow_smooth_trace (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => b s.toNNReal)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) :
    Tendsto (fun y : ℝ => inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I))
      (𝓝[>] 0) (𝓝 (trace 1 b T)) := by
  have he := inverseFlow_tip_limit_of_smooth_driver b T b' hd hL hb
  simpa only [trace,one_mul,driverValue,Real.toNNReal_coe] using tendsto_nhds_limUnder he

theorem inverseFlow_smooth_trace_error (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => b s.toNNReal)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L a : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (haT : a ≤ T)
    (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) (hsmall : L^2*a ≤ 1)
    {y : ℝ} (hy : 0 < y) :
    dist (inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I)) (trace 1 b T) ≤
      y*Real.exp ((4*(Real.sqrt a)⁻¹^2)*((T : ℝ)-a)) := by
  have ht := tendsto_inverseFlow_smooth_trace b T b' hd hL hb
  have hr : Tendsto (fun v : ℝ => |y-v| *
      Real.exp ((4*(Real.sqrt a)⁻¹^2)*((T : ℝ)-a))) (𝓝[>] 0)
      (𝓝 (y*Real.exp ((4*(Real.sqrt a)⁻¹^2)*((T : ℝ)-a)))) := by
    have hid : Tendsto (fun v : ℝ => v) (𝓝[>] 0) (𝓝 (0 : ℝ)) := nhdsWithin_le_nhds
    have h := (hid.const_sub y).abs.mul_const
      (Real.exp ((4*(Real.sqrt a)⁻¹^2)*((T : ℝ)-a)))
    simpa only [sub_zero,abs_of_pos hy] using h
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds.dist ht) hr
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact inverseFlow_vertical_distance_of_smooth_driver b T b' hd hL ha haT hb hsmall hy hv

end SLEExactGauge.Target

end

end OAI
