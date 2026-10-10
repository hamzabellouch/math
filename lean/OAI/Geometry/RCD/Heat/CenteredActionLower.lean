import OAI.Geometry.RCD.Heat.ScaledHeatActionLimit

namespace OAI

/-! # Sharp action lower bound from a zero reference trajectory -/

open Set Filter Metric
open scoped Topology
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem HeatActionLimit.lower_of_center_zero {z : X} (H : HeatActionLimit z)
    (hz : ∀ s ∈ Ioo (0:ℝ) 1, H.potential s z = 0)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (x : X) :
    -(dist z x)^2/(2*t) ≤ H.potential t x := by
  have hc : ContinuousAt (fun s : ℝ => (dist z x)^2/(2*(t-s))) 0 := by
    have hd : 2*(t-(0:ℝ)) ≠ 0 := by nlinarith [ht.1]
    fun_prop (disch := exact hd)
  have hl : Tendsto (fun s : ℝ => (dist z x)^2/(2*(t-s))) (𝓝[>] 0)
      (𝓝 ((dist z x)^2/(2*t))) := by
    simpa only [sub_zero] using hc.continuousWithinAt.tendsto (s := Ioi (0:ℝ))
  have he : ∀ᶠ s in 𝓝[>] (0:ℝ), -H.potential t x ≤ (dist z x)^2/(2*(t-s)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds ht.1)] with s hs hst
    have hh := H.action s t hs hst ht.2 z x
    rw [hz s ⟨hs,hst.trans ht.2⟩,zero_sub] at hh
    exact hh
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds hl he
  simpa only [neg_div,neg_neg] using neg_le_neg hh

end RegularPointCoordinates

end OAI
