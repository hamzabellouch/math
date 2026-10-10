import OAI.Geometry.EinsteinFour.MetricChartLipschitz
import OAI.Geometry.EinsteinFour.RiemannianVolumeFinite

namespace OAI

/-! A nonempty smooth Riemannian four-manifold has positive Hausdorff
volume. The proof compares a small neighborhood with its Euclidean chart
using the actual Riemannian distance. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem volumeMeasure_pos [Nonempty M] (g : SmoothMetric M) :
    0 < volumeMeasure g Set.univ := by
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
  obtain ⟨c⟩ := ‹Nonempty M›
  obtain ⟨s, hs, _hsource, K, hK⟩ := exists_metric_chart_lipschitz g c
  have hLip : LipschitzOnWith K (chartAt FourSpace c) s := by
    intro x hx y hy
    exact hK x hx y hy
  have himage : (chartAt FourSpace c) '' s ∈ 𝓝 (chartAt FourSpace c c) :=
    (chartAt FourSpace c).image_mem_nhds (mem_chart_source FourSpace c) hs
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp himage
  have himage_pos : 0 < ν ((chartAt FourSpace c) '' s) :=
    lt_of_lt_of_le (Metric.isOpen_ball.measure_pos ν (Metric.nonempty_ball.mpr hr))
      (measure_mono hball)
  have hs_pos : 0 < μ s := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have h := hLip.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 4)
    change ν ((chartAt FourSpace c) '' s) ≤ (K : ℝ≥0∞) ^ (4 : ℝ) * μ s at h
    rw [hz, mul_zero] at h
    exact (not_le_of_gt himage_pos) h
  have hmass : 0 < μ Set.univ := hs_pos.trans_le (measure_mono (subset_univ s))
  change 0 < (ENNReal.ofReal (Real.pi ^ 2 / 32) • μ) Set.univ
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hmass.ne'

theorem actual_finitePositiveVolume [Nonempty M] [CompactSpace M] (g : SmoothMetric M) :
    FinitePositiveVolume g :=
  ⟨volumeMeasure_pos g, volumeMeasure_lt_top g⟩

end
end PositiveEinsteinFour.Geometry

end OAI
