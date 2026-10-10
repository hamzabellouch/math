import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalAngular

namespace OAI

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

def unitCoordinate (p : A.centers) (q : Space)
    (u : MetricUnit (hermitianMetric J α hs ht)) : UnitaryFrame.W :=
  coordinateDecode J α ht A E p q
    (unitFrameDirection A J α ht E (hermitianMetric J α hs ht) u)

include hE in
lemma unitCoordinate_line (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht)) (hu : (extChartAt Model p.val).symm q = u.val.proj) :
    ∃ a : UnitaryFrame.V, ‖a‖ = 1 ∧ unitCoordinate A J α hs ht E p q u = UnitaryFrame.line a := by
  obtain ⟨a,ha,he,-,-⟩ := exists_unitDual_coordinate_line A J α hs ht E hE p hq u hu
  refine ⟨a,ha,?_⟩
  unfold unitCoordinate
  rw [← unitDual_encode A J α hs ht E hE]
  exact he

include hE in
lemma coordinateWedge_actual (p : A.centers) {q y : Space}
    (hq : q ∈ (E p).chart.domain) (hy : y ∈ (E p).chart.domain)
    (u v : MetricUnit (hermitianMetric J α hs ht))
    (hu : (extChartAt Model p.val).symm y = u.val.proj)
    (hv : (extChartAt Model p.val).symm q = v.val.proj)
    (K : Space × Space → UnitaryFrame.W →L[ℝ] UnitaryFrame.W) :
    unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
      (coordinateMatrix J α ht A E p K (q,y)
        (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) =
      ⟪unitCoordinate A J α hs ht E p y u,
        K (q,y) (UnitaryFrame.star (unitCoordinate A J α hs ht E p q v))⟫ := by
  obtain ⟨a,-,hea,-,hpa⟩ := exists_unitDual_coordinate_line A J α hs ht E hE p hy u hu
  obtain ⟨b,-,heb,hdb,-⟩ := exists_unitDual_coordinate_line A J α hs ht E hE p hq v hv
  have ha : unitCoordinate A J α hs ht E p y u = UnitaryFrame.line a := by
    unfold unitCoordinate
    rw [← unitDual_encode A J α hs ht E hE]
    exact hea
  have hb : unitCoordinate A J α hs ht E p q v = UnitaryFrame.line b := by
    unfold unitCoordinate
    rw [← unitDual_encode A J α hs ht E hE]
    exact heb
  rw [ha,hb,unitFrameFunctional_eq A J α hs ht E hE,← unitDual_starDirection A J α hs ht E hE]
  change framePairing A J α ht E (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val
    u.val.proj (coordinateEncode J α ht A E p y (K (q,y)
      (coordinateDecode J α ht A E p q _))) = _
  rw [hdb,hpa]

def normalAngular (p : A.centers) (z : Space × Space)
    (u v : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  ‖unitCoordinate A J α hs ht E p
      (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) u -
    normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
      (unitCoordinate A J α hs ht E p z.1 v)‖

include hE in
lemma gammaNormalWedge_actual_angular (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ z ∈ (E p).normalCompact,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
      (extChartAt Model p.val).symm z.1 = v.val.proj →
      (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
        (normalAngular A J α hs ht E p z u v)^2 -
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
  obtain ⟨a,ha,hea⟩ := unitCoordinate_line A J α hs ht E hE p hd.2 u hu
  obtain ⟨b,hb,heb⟩ := unitCoordinate_line A J α hs ht E hE p hd.1 v hv
  rw [coordinateWedge_actual A J α hs ht E hE p hd.1 hd.2 u v hu hv,
    gammaPartitionLeading_apply J α ht A E hr T p hz,smul_apply,hea,heb]
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
  have h := hbound N r hr T (coordinatePartition A p) (E p).normalCutoff z.1 hz.1 z.2
    (mul_nonneg hp.1 hχ)
    ((mul_le_mul_of_nonneg_right hp.2 hχ).trans
      (by simpa only [one_mul] using (E p).normalCutoff.le_one (x := z.2))) a b ha hb
  rw [leadingCoordinate_gamma J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension hr] at h
  simpa only [normalAngular,hea,heb,smul_apply,UnitaryFrame.star_smul,inner_smul_right] using h

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
