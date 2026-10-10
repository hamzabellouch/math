import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeIntrinsicUnitLine
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaLinearTransfer

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge HodgeNormalSymbol NormalJets NormalMetricCalculus Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma compact_normalGauge_angular_global (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : Space,
      ∀ v w : Space, ‖v‖ = 1 → ‖w‖ = 1 →
        (1/2 : ℝ)*‖UnitaryFrame.line v-normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w)‖^2 - C*‖z‖^2 ≤
        ⟪UnitaryFrame.line v,UnitaryFrame.star (normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w))⟫ := by
  obtain ⟨C,hC,ρ,hρ,hsmall⟩ := compact_normalGauge_angular J α ht p D g B hs hg hB K hK hactual
  refine ⟨max C (2/ρ^2),le_trans hC (le_max_left _ _),?_⟩
  intro q hq z v w hv hw
  by_cases hz : ‖z‖ ≤ ρ
  · have hh := hsmall q hq z hz v w hv hw
    have hm := mul_le_mul_of_nonneg_right (le_max_left C (2/ρ^2)) (sq_nonneg ‖z‖)
    linarith
  · rw [normalGauge_angular J α ht p D g B hs hg hB (hactual q hq) z v w hv hw]
    have hn := ContinuousLinearMap.norm_map_of_mem_unitary
      (normalGauge_unitary J α ht p D g B hs hg hB (hactual q hq) z) UnitaryFrame.fundamental
    have hb := norm_sub_le UnitaryFrame.fundamental
      (normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental)
    rw [hn] at hb
    have hF := UnitaryFrame.fundamental_norm_sq
    have hsq : ‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖^2 ≤ 8 := by
      have hnonneg : 0 ≤ 2*‖UnitaryFrame.fundamental‖ := by positivity
      have hm := sq_le_sq₀ (norm_nonneg _) hnonneg |>.mpr (by linarith :
        ‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖ ≤
          2*‖UnitaryFrame.fundamental‖)
      nlinarith
    have hzρ : ρ^2 ≤ ‖z‖^2 := by nlinarith [lt_of_not_ge hz]
    have h2 : 2 ≤ (2/ρ^2)*‖z‖^2 := by
      calc
        2 = (2/ρ^2)*ρ^2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hzρ (by positivity)
    have hm := mul_le_mul_of_nonneg_right (le_max_right C (2/ρ^2)) (sq_nonneg ‖z‖)
    linarith

lemma leadingCoordinate_gamma_angular_global (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K) (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, ∀ r : ℝ, 0 < r → ∀ T : ℝ, ∀ ψ χ : Space → ℝ,
      ∀ q ∈ K, ∀ z : Space,
      0 ≤ ψ q*χ z → ψ q*χ z ≤ 1 →
      ∀ v w : Space, ‖v‖ = 1 → ‖w‖ = 1 →
      (1/2 : ℝ)*(ψ q*χ z*HodgeKernelBounds.leading r T ‖z‖)*
        ‖UnitaryFrame.line v-normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w)‖^2 -
          (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z‖/r)^N ≤
        ⟪UnitaryFrame.line v,UnitaryFrame.star
          (((1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s •
            leadingCoordinate J α ht p D g B ψ χ (r^2*s) (q,z))) (UnitaryFrame.line w))⟫ := by
  obtain ⟨C,hC,hangular⟩ := compact_normalGauge_angular_global J α ht p D g B hs hg hB K hK hactual
  refine ⟨C,hC,?_⟩
  intro N r hr T ψ χ q hq z hp hp1 v w hv hw
  rw [leadingCoordinate_gamma J α ht p D g B hr]
  simp only [smul_apply,UnitaryFrame.star_smul,inner_smul_right]
  have hl := HodgeKernelBounds.leading_nonneg r T ‖z‖
  have ha := mul_le_mul_of_nonneg_left (hangular q hq z v w hv hw) (mul_nonneg hp hl)
  have he : (ψ q*χ z*HodgeKernelBounds.leading r T ‖z‖)*(C*‖z‖^2) ≤
      (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z‖/r)^N := by
    calc
      _ = C*((ψ q*χ z)*(‖z‖^2*HodgeKernelBounds.leading r T ‖z‖)) := by ring
      _ ≤ C*(‖z‖^2*HodgeKernelBounds.leading r T ‖z‖) :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) hl) hp1) hC
      _ ≤ C*(HodgeKernelBounds.leadingConstant (N+2)*(r⁻¹)^2/(1+‖z‖/r)^N) :=
        mul_le_mul_of_nonneg_left (HodgeKernelBounds.leading_quadratic_upper N hr (norm_nonneg z) T) hC
      _ = _ := by ring
  nlinarith

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma gammaNormalWedge_angular (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ z ∈ (E p).normalCompact,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
      (extChartAt Model p.val).symm z.1 = v.val.proj →
      ∃ a b : UnitaryFrame.V, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
        ‖UnitaryFrame.line a-normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
          (UnitaryFrame.line b)‖^2 -
        (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z.2‖/r)^N ≤
        unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
          (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
            (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
            (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by
  obtain ⟨C,hC,hbound⟩ := leadingCoordinate_gamma_angular_global J α ht p.val (E p).chart
    (E p).metricExtension (E p).frameExtension hs (E p).metric_smooth (E p).frame_smooth
    (Metric.closedBall (extChartAt Model p.val p.val) (E p).radius) (isCompact_closedBall _ _)
    (fun _ hq => (E p).actual hq)
  refine ⟨C,hC,fun N r hr T z hz u v hu hv => ?_⟩
  have hd := (E p).physicalCompact_domain ⟨z,hz,rfl⟩
  change z.1 ∈ (E p).chart.domain ∧
    normalMap (E p).metricExtension (E p).frameExtension z.1 z.2 ∈ (E p).chart.domain at hd
  obtain ⟨a,b,ha,hb,he⟩ := coordinateWedge_lines A J α hs ht E hE p hd.1 hd.2 u v hu hv
  refine ⟨a,b,ha,hb,?_⟩
  rw [he,gammaPartitionLeading_apply J α ht A E hr T p hz,smul_apply]
  have hstar := normalGauge_commutes J α ht p.val (E p).chart (E p).metricExtension
    (E p).frameExtension hs (E p).metric_smooth (E p).frame_smooth
    (((E p).actual hz.1).center J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension).1 z.2
  have hstar' := congrArg (fun L : UnitaryFrame.W →L[ℝ] UnitaryFrame.W => L (UnitaryFrame.line b)) hstar
  change normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
    (UnitaryFrame.star (UnitaryFrame.line b)) =
      UnitaryFrame.star (normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
        (UnitaryFrame.line b)) at hstar'
  rw [hstar',inner_smul_right]
  have hp := coordinatePartition_bounds A p z.1
  have hχ := (E p).normalCutoff.nonneg (x := z.2)
  have hχ1 := (E p).normalCutoff.le_one (x := z.2)
  have h := hbound N r hr T (coordinatePartition A p) (E p).normalCutoff z.1 hz.1 z.2
    (mul_nonneg hp.1 hχ)
    ((mul_le_mul_of_nonneg_right hp.2 hχ).trans (by simpa only [one_mul] using hχ1)) a b ha hb
  rw [leadingCoordinate_gamma J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension hr] at h
  simpa only [smul_apply,UnitaryFrame.star_smul,inner_smul_right] using h

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
