import OAI.Geometry.EinsteinFour.RiemannianVolumePositive
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! The actual Riemannian volume has full support.  This follows directly
from the local Lipschitz chart comparison, without an assumed density formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem volumeMeasure_open_pos (g : SmoothMetric M) (U : Set M)
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < volumeMeasure g U := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  let μ : Measure M := Measure.hausdorffMeasure 4
  let ν : Measure FourSpace := Measure.hausdorffMeasure 4
  let : Measure.IsAddHaarMeasure ν := by
    simpa [ν, FourSpace] using
      (inferInstance : Measure.IsAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ FourSpace) : Measure FourSpace))
  obtain ⟨c, hc⟩ := hne
  obtain ⟨s, hs, _, K, hK⟩ := exists_metric_chart_lipschitz g c
  have hLip : LipschitzOnWith K (chartAt FourSpace c) (s ∩ U) := by
    intro x hx y hy
    exact hK x hx.1 y hy.1
  have himage : (chartAt FourSpace c) '' (s ∩ U) ∈ 𝓝 (chartAt FourSpace c c) :=
    (chartAt FourSpace c).image_mem_nhds (mem_chart_source FourSpace c)
      (Filter.inter_mem hs (hU.mem_nhds hc))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp himage
  have himage_pos : 0 < ν ((chartAt FourSpace c) '' (s ∩ U)) :=
    lt_of_lt_of_le (Metric.isOpen_ball.measure_pos ν (Metric.nonempty_ball.mpr hr))
      (measure_mono hball)
  have hs_pos : 0 < μ (s ∩ U) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have h := hLip.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 4)
    change ν ((chartAt FourSpace c) '' (s ∩ U)) ≤
      (K : ℝ≥0∞) ^ (4 : ℝ) * μ (s ∩ U) at h
    rw [hz, mul_zero] at h
    exact (not_le_of_gt himage_pos) h
  have hmass : 0 < μ U := hs_pos.trans_le (measure_mono inter_subset_right)
  change 0 < (ENNReal.ofReal (Real.pi ^ 2 / 32) • μ) U
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hmass.ne'

theorem volumeMeasure_isOpenPosMeasure (g : SmoothMetric M) :
    (volumeMeasure g).IsOpenPosMeasure :=
  ⟨fun U hU hne => (volumeMeasure_open_pos g U hU hne).ne'⟩

theorem normalizedVolume_isOpenPosMeasure [Nonempty M] [CompactSpace M]
    (g : SmoothMetric M) : (normalizedVolume g).IsOpenPosMeasure := by
  let := volumeMeasure_isOpenPosMeasure g
  exact Measure.isOpenPosMeasure_smul _
    (ENNReal.inv_ne_zero.mpr (actual_finitePositiveVolume g).finite.ne)

end
end PositiveEinsteinFour.Geometry

end OAI
