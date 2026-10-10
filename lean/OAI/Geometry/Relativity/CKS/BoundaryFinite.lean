import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.TailEnergy
import OAI.Geometry.Relativity.CKS.ChartDistance
import OAI.Geometry.Relativity.CKS.BoundaryPlane

namespace OAI

noncomputable section
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal
namespace CKSIntrinsicGeometry
attribute [local instance] halfSpaceDimension_neZero

section Charts
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 1 M]

lemma boundary_chart_zero (x y : M) (hy : y ∈ (extChartAt I3 x).source)
    (hS : y ∈ I3.boundary M) : (extChartAt I3 x y) 0 = 0 := by
  have hychart : y ∈ (chartAt H3 x).source := by simpa using hy
  have hyrange : extChartAt I3 x y ∈ range I3 :=
    (extChartAt_target_subset_range x) ((extChartAt I3 x).map_source hy)
  have hnonneg : 0 ≤ (extChartAt I3 x y) 0 := by
    simpa only [I3, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hyrange
  have hnot : ¬I3.IsInteriorPoint y :=
    (I3.isBoundaryPoint_iff_not_isInteriorPoint y).mp hS
  have hle : (extChartAt I3 x y) 0 ≤ 0 := by
    by_contra h
    have hpos : 0 < (extChartAt I3 x y) 0 := lt_of_not_ge h
    have hint : extChartAt I3 x y ∈ interior (range I3) := by
      simpa only [I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hpos
    apply hnot
    apply (I3.isInteriorPoint_iff_of_mem_atlas one_ne_zero (chart_mem_atlas H3 x) hychart).mpr
    exact (chartAt H3 x).mem_interior_extend_target ((chartAt H3 x).map_source hychart) hint
  exact le_antisymm hle hnonneg
end Charts

section Distance
variable {M : Type*} [EMetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace H3 M] [IsManifold I3 1 M]
  [RiemannianBundle (fun x : M => TangentSpace I3 x)]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace I3 x)]
  [IsRiemannianManifold I3 M]

theorem boundary_hausdorff_finiteAt (x : M) :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure M).FiniteAtFilter (𝓝[I3.boundary M] x) := by
  obtain ⟨C, r, hC, hr, htarget, hdist⟩ := chart_inverse_distance_bound I3 x
  let s : Set E3 := ball (extChartAt I3 x x) r ∩ {q : E3 | q 0 = 0}
  have hsub : s ⊆ ball (extChartAt I3 x x) r ∩ range I3 := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    have hz : q 0 = 0 := hq.2
    rw [show range I3 = {q : E3 | 0 ≤ q 0} from range_modelWithCornersEuclideanHalfSpace 3]
    change 0 ≤ q 0
    rw [hz]
  have hlip : LipschitzOnWith C (extChartAt I3 x).symm s := by
    intro u hu v hv
    rw [IsRiemannianManifold.out (I := I3)]
    exact hdist u (hsub hu) v (hsub hv)
  have hsfinite : (Measure.hausdorffMeasure (2 : ℝ) : Measure E3) s < ⊤ :=
    boundary_plane_ball_area_finite _ _
  have himage : (Measure.hausdorffMeasure (2 : ℝ) : Measure M)
      ((extChartAt I3 x).symm '' s) < ⊤ := by
    refine (hlip.hausdorffMeasure_image_le (by norm_num)).trans_lt ?_
    have hp : (C : ℝ≥0∞) ^ (2 : ℝ) < ⊤ := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      exact ENNReal.pow_lt_top ENNReal.coe_lt_top
    exact ENNReal.mul_lt_top hp hsfinite
  have hpre : (extChartAt I3 x) ⁻¹' (ball (extChartAt I3 x x) r ∩ range I3) ∈ 𝓝 x := by
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (by simp)
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (ball_mem_nhds _ hr)
  let V := (extChartAt I3 x).source ∩
    (extChartAt I3 x) ⁻¹' (ball (extChartAt I3 x x) r ∩ range I3)
  have hV : V ∈ 𝓝 x :=
    inter_mem (by simpa using chart_source_mem_nhds H3 x) hpre
  refine ⟨V ∩ I3.boundary M, inter_mem (nhdsWithin_le_nhds hV) self_mem_nhdsWithin, ?_⟩
  apply lt_of_le_of_lt (measure_mono ?_) himage
  intro y hy
  refine ⟨extChartAt I3 x y, ?_, (extChartAt I3 x).left_inv hy.1.1⟩
  exact ⟨hy.1.2.1, boundary_chart_zero x y hy.1.1 hy.2⟩

theorem compact_boundary_hausdorff_finite (hS : IsCompact (I3.boundary M)) :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure M) (I3.boundary M) < ⊤ := by
  exact hS.measure_lt_top_of_nhdsWithin (fun x _ => boundary_hausdorff_finiteAt x)
end Distance
end CKSIntrinsicGeometry

end

end OAI
