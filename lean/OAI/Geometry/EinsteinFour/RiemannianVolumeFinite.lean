import OAI.Geometry.EinsteinFour.MetricChartDistance
import OAI.Geometry.EinsteinFour.RiemannianVolume

namespace OAI

/-! Compactness and bounded inverse-chart differentials imply finiteness
of the actual four-dimensional Riemannian Hausdorff measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

private theorem fourSpace_hausdorff_haar :
    Measure.IsAddHaarMeasure (Measure.hausdorffMeasure 4 : Measure FourSpace) := by
  simpa [FourSpace] using
    (inferInstance : Measure.IsAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ FourSpace) : Measure FourSpace))

theorem volumeMeasure_lt_top [CompactSpace M] (g : SmoothMetric M) :
    volumeMeasure g Set.univ < ⊤ := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  let μ : Measure M := Measure.hausdorffMeasure 4
  have hlocal (c : M) : μ.FiniteAtFilter (𝓝 c) := by
    obtain ⟨r, hr, K, _htarget, hK⟩ := exists_metric_chart_bound g c
    let B := Metric.closedBall (chartAt FourSpace c c) r
    have hB : (Measure.hausdorffMeasure 4 : Measure FourSpace) B < ⊤ := by
      let _ := fourSpace_hausdorff_haar
      exact (isCompact_closedBall _ _).measure_lt_top
    have hLip : LipschitzOnWith K (chartAt FourSpace c).symm B := by
      intro x hx y hy
      exact hK x hx y hy
    have hfinite : μ ((chartAt FourSpace c).symm '' B) < ⊤ := by
      apply lt_of_le_of_lt (hLip.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 4))
      rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hB
    refine ⟨(chartAt FourSpace c).symm '' B, ?_, hfinite⟩
    have hc : chartAt FourSpace c c ∈ (chartAt FourSpace c).target :=
      (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    have hn := (chartAt FourSpace c).symm.image_mem_nhds hc
      (Metric.closedBall_mem_nhds (chartAt FourSpace c c) hr)
    simpa only [(chartAt FourSpace c).left_inv (mem_chart_source FourSpace c)] using hn
  let _ : IsLocallyFiniteMeasure μ := ⟨hlocal⟩
  have hfinite : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
  change (ENNReal.ofReal (Real.pi ^ 2 / 32) • μ) Set.univ < ⊤
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite

end
end PositiveEinsteinFour.Geometry

end OAI
