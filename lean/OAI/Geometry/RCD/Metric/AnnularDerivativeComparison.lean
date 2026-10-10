import OAI.Geometry.RCD.Metric.AnnularVolumeRatio

namespace OAI

/-! # Passing sharp annular volume comparison to radial derivatives -/

open Set Filter Metric MeasureTheory
open scoped Topology

namespace RegularPointCoordinates

theorem derivative_density_le_of_annular_comparison
    {V w : ℝ → ℝ} {x y α vx vy : ℝ} (hα : 0 < α)
    (hx : HasDerivAt V vx x) (hy : HasDerivAt V vy y)
    (hwx : ContinuousAt w x) (hwy : ContinuousAt w y)
    (hbound : ∀ h : ℝ, 0 < h →
      (α * w (x + α * h)) * (V (y + h) - V y) ≤
        w (y + h) * (V (x + α * h) - V x)) :
    w x * vy ≤ w y * vx := by
  have hzero : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmap : HasDerivAt (fun h : ℝ => x + α * h) α 0 := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id (0 : ℝ)).const_mul α).const_add x
  have hx' : HasDerivAt V vx (x + α * 0) := by simpa only [mul_zero, add_zero] using hx
  have hG : HasDerivAt (fun h : ℝ => V (x + α * h)) (vx * α) 0 :=
    hx'.comp 0 hmap
  have hdx : Tendsto (fun h : ℝ => h⁻¹ * (V (x + α * h) - V x))
      (𝓝[>] 0) (𝓝 (vx * α)) := by
    simpa only [zero_add, mul_zero, add_zero, smul_eq_mul] using hG.tendsto_slope_zero_right
  have hdy : Tendsto (fun h : ℝ => h⁻¹ * (V (y + h) - V y))
      (𝓝[>] 0) (𝓝 vy) := by
    simpa only [smul_eq_mul] using hy.tendsto_slope_zero_right
  have hwx' : Tendsto (fun h : ℝ => w (x + α * h)) (𝓝[>] 0) (𝓝 (w x)) := by
    apply hwx.tendsto.comp
    simpa only [mul_zero, add_zero] using (hzero.const_mul α).const_add x
  have hwy' : Tendsto (fun h : ℝ => w (y + h)) (𝓝[>] 0) (𝓝 (w y)) := by
    apply hwy.tendsto.comp
    simpa only [add_zero] using hzero.const_add y
  have hlim : (α * w x) * vy ≤ w y * (vx * α) := by
    apply le_of_tendsto_of_tendsto ((hwx'.const_mul α).mul hdy) (hwy'.mul hdx)
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hm := mul_le_mul_of_nonneg_left (hbound h hh) (inv_nonneg.mpr hh.le)
    convert hm using 1 <;> ring
  apply (mul_le_mul_iff_right₀ hα).mp
  nlinarith only [hlim]

end RegularPointCoordinates

end OAI
