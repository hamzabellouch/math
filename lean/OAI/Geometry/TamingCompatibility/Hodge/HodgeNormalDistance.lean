import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeWedgeQuantitative
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalAngular

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame Set
open scoped Manifold ContDiff Topology NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (E : ParametrixData J α ht p)

omit [SecondCountableTopology X] in
lemma normalMap_physical_distance :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z ∈ E.normalCompact,
      dist ((extChartAt Model p).symm (normalMap E.metricExtension E.frameExtension z.1 z.2))
        ((extChartAt Model p).symm z.1) ≤ C*‖z.2‖ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let L := Prod.fst '' E.physicalCompact ∪ Prod.snd '' E.physicalCompact
  have hL : IsCompact L := (E.physicalCompact_compact.image continuous_fst).union
    (E.physicalCompact_compact.image continuous_snd)
  have hLt : L ⊆ (extChartAt Model p).target := by
    rintro q (⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩)
    · exact E.chart.domain_subset (E.physicalCompact_domain hw).1
    · exact E.chart.domain_subset (E.physicalCompact_domain hw).2
  obtain ⟨C,hC⟩ := chartInverse_compact_lipschitz J α hs ht p L hL hLt
  obtain ⟨B,hB,hmap⟩ := normalMap_compact_bound E.metricExtension E.frameExtension
    E.metric_smooth E.frame_smooth (Metric.closedBall (extChartAt Model p p) E.radius)
    (isCompact_closedBall _ _) E.radius_pos.le
  refine ⟨max ((C:ℝ)*B) 1,le_max_right _ _,fun z hz => ?_⟩
  have hp : (z.1,normalMap E.metricExtension E.frameExtension z.1 z.2) ∈ E.physicalCompact :=
    ⟨z,hz,rfl⟩
  have hqL : z.1 ∈ L := Or.inl ⟨_,hp,rfl⟩
  have hyL : normalMap E.metricExtension E.frameExtension z.1 z.2 ∈ L := Or.inr ⟨_,hp,rfl⟩
  have hd := hC.dist_le_mul _ hyL _ hqL
  rw [dist_eq_norm] at hd
  calc
    _ ≤ (C:ℝ)*‖normalMap E.metricExtension E.frameExtension z.1 z.2-z.1‖ := hd
    _ ≤ (C:ℝ)*(B*‖z.2‖) := mul_le_mul_of_nonneg_left
      (hmap z.1 hz.1 z.2 (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2)) C.coe_nonneg
    _ ≤ max ((C:ℝ)*B) 1*‖z.2‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
lemma weighted_negative_lower {f W C L D : ℝ} (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hD : 0 < D) (hbound : W ≤ L*D) (hlower : -C/D ≤ f) : -(L*C) ≤ W*f := by
  calc
    -(L*C) = (L*D)*(-C/D) := by field_simp
    _ ≤ W*(-C/D) := mul_le_mul_of_nonpos_right hbound (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) hD.le)
    _ ≤ W*f := mul_le_mul_of_nonneg_left hlower hW

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma gammaNormalWedge_weighted_lower (p : A.centers) (N : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ z ∈ (E p).normalCompact,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
      (extChartAt Model p.val).symm z.1 = v.val.proj →
      -C/r^2 ≤ VolterraBounds.weight N (r^2) u.val.proj v.val.proj *
        unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
          (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
            (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
            (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,hC,hangular⟩ := gammaNormalWedge_angular A J α hs ht E hE p
  obtain ⟨L,hL,hdist⟩ := normalMap_physical_distance J α hs ht p.val (E p)
  have hLC := (HodgeKernelBounds.leadingConstant_pos (N+2)).le
  refine ⟨L^N*(C*HodgeKernelBounds.leadingConstant (N+2)),by positivity,?_⟩
  intro r hr T z hz u v hu hv
  obtain ⟨a,b,ha,hb,hbound⟩ := hangular N r hr T z hz u v hu hv
  have hp := (coordinatePartition_bounds A p z.1).1
  have hχ := (E p).normalCutoff.nonneg (x := z.2)
  have hlead := HodgeKernelBounds.leading_nonneg r T ‖z.2‖
  have hpositive : 0 ≤ (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*
      HodgeKernelBounds.leading r T ‖z.2‖)*
      ‖UnitaryFrame.line a-normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
        (UnitaryFrame.line b)‖^2 := by positivity
  have hlower : -((C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2)/(1+‖z.2‖/r)^N ≤
      unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
        (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
          (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
          (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by rw [neg_div]; linarith only [hbound,hpositive]
  have hd : dist u.val.proj v.val.proj ≤ L*‖z.2‖ := by rw [← hu,← hv]; exact hdist z hz
  have hw := weight_of_dist_bound N (sq_pos_of_pos hr) hL (norm_nonneg z.2) u.val.proj v.val.proj hd
  rw [Real.sqrt_sq hr.le] at hw
  have h := weighted_negative_lower (by positivity : 0 ≤ (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2)
    (VolterraBounds.weight_pos N (sq_pos_of_pos hr) u.val.proj v.val.proj).le
    (by positivity : 0 < (1+‖z.2‖/r)^N) hw hlower
  convert h using 1
  simp only [div_eq_mul_inv,inv_pow]
  ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma gammaPatchWedge_weighted_lower (p : A.centers) (N : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      -C/r^2 ≤ VolterraBounds.weight N (r^2) u.val.proj v.val.proj *
        unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
          (ManifoldKernelExtension.push p.val
            (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p))
            (v.val.proj,u.val.proj) (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,hC,hbound⟩ := gammaNormalWedge_weighted_lower A J α hs ht E hE p N
  refine ⟨C,hC,fun r hr T u v => ?_⟩
  let e := extChartAt Model p.val
  have hneg : -C/r^2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) (sq_nonneg r)
  by_cases huv : (v.val.proj,u.val.proj) ∈ e.source ×ˢ e.source
  · dsimp only [e] at huv
    rw [ManifoldKernelExtension.push,ite_eq_left huv]
    by_cases hK : gammaPartitionLeading J α ht A E T r p (e v.val.proj,e u.val.proj) = 0
    · dsimp only [e] at hK
      simpa only [coordinateMatrix,hK,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,
        zero_apply,map_zero,mul_zero] using hneg
    · obtain ⟨z,hz,he⟩ := gammaPartitionLeading_support J α ht A E hE T r p hK
      have hq : z.1 = e v.val.proj := congrArg Prod.fst he
      have hy : normalMap (E p).metricExtension (E p).frameExtension z.1 z.2 = e u.val.proj := congrArg Prod.snd he
      have hu : e.symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj := by
        rw [hy,e.left_inv huv.2]
      have hv : e.symm z.1 = v.val.proj := by rw [hq,e.left_inv huv.1]
      have h := hbound r hr T z hz u v hu hv
      rw [hy,hq] at h
      exact h
  · dsimp only [e] at huv
    simpa only [ManifoldKernelExtension.push,ite_eq_right huv,zero_apply,map_zero,mul_zero] using hneg

include hE in
lemma globalLeadingWedge_weighted_lower (N : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      -C/r^2 ≤ VolterraBounds.weight N (r^2) u.val.proj v.val.proj *
        unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
          (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v := by
  classical
  dsimp only
  let := geometricMetricSpace J α hs ht
  choose C hC hb using fun p : A.centers => gammaPatchWedge_weighted_lower A J α hs ht E hE p N
  refine ⟨∑ p : A.centers, C p,Finset.sum_nonneg (fun p _ => hC p),fun r hr T u v => ?_⟩
  unfold unitWedgeKernel
  rw [globalLeading_gamma_sum J α ht A E hr T]
  simp only [sum_apply,map_sum,Finset.mul_sum]
  calc
    -(∑ p : A.centers, C p)/r^2 = ∑ p : A.centers, -C p/r^2 := by
      simp only [neg_div,Finset.sum_div,Finset.sum_neg_distrib]
    _ ≤ _ := Finset.sum_le_sum (fun p _ => hb p r hr T u v)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
