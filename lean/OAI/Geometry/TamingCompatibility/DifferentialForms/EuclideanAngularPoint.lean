import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.EuclideanCoordinateLine
import OAI.Geometry.TamingCompatibility.Hodge.HodgePatchContinuity

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def euclideanLine (p : A.centers) (u : MetricUnit (hermitianMetric J α hs ht)) : W :=
  wedge (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)

include hE in
lemma unitCoordinate_exterior_norm (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).actualDomain) :
    ‖exteriorTransform ((E p).frameExtension (unitChartBase J α hs ht p.val u))
      (unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u)‖ =
        unitChartArea J α hs ht p.val u := by
  rw [(E p).frame_actual _ hq,exteriorTransform_frame,
    unitCoordinate_wedgeTransform A J α hs ht E hE p u hu ((E p).actual_subset hq)]
  have hn := unitChartVector_ne_zero J α hs ht p.val u hu
  exact norm_wedge_area _ _ hn (normalPart_complex_ne_zero _
    (coordinateJ_square J p.val ((extChartAt Model p.val).map_source hu)) hn)

include hE in
lemma unitCoordinate_exterior_first (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).actualDomain) :
    first (exteriorTransform ((E p).frameExtension (unitChartBase J α hs ht p.val u))
      (unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u)) =
        euclideanLine A J α hs ht p u := by
  rw [(E p).frame_actual _ hq,exteriorTransform_frame]
  exact unitCoordinate_normalized_wedgeTransform A J α hs ht E hE p u hu ((E p).actual_subset hq)

include hE in

lemma euclidean_angular_point (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ uv ∈ angularDomain A J α hs ht E p,
      ‖(angularCoordinates A J α hs ht E p uv).2‖ ≤ r →
      ‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖ ≤
        C*(normalAngular A J α hs ht E p (angularCoordinates A J α hs ht E p uv) uv.1 uv.2 +
          ‖(angularCoordinates A J α hs ht E p uv).2‖) := by
  let K := Prod.snd '' (E p).physicalCompact
  have hK : IsCompact K := (E p).physicalCompact_compact.image continuous_snd
  have hKT : K ⊆ (extChartAt Model p.val).target := by
    rintro y ⟨xy,hxy,rfl⟩
    exact (E p).chart.domain_subset ((E p).physicalCompact_domain hxy).2
  obtain ⟨m,M,hm,_,harea⟩ := unitChartArea_bounds J α hs ht p.val hK hKT
  obtain ⟨L,hL,r,hr,hlin⟩ := euclidean_transport_linear J α ht p.val (E p).chart
    (E p).metricExtension (E p).frameExtension hs (E p).metric_smooth (E p).frame_smooth
    (Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (isCompact_closedBall _ _) (fun q hq => (E p).actual hq)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (exteriorTransform_smooth (E p).frame_smooth).continuous.continuousOn
  let C := (2/m)*max (max B 0) L
  have hC : 0 ≤ C := mul_nonneg (by positivity) (le_max_of_le_left (le_max_right _ _))
  refine ⟨C,hC,r,hr,?_⟩
  intro uv huv hz
  let z := angularCoordinates A J α hs ht E p uv
  have hzn := angularCoordinates_mem A J α hs ht E p huv
  have he := angularCoordinates_chart A J α hs ht E p huv
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change z.1 = unitChartBase J α hs ht p.val uv.2 at he1
  change normalMap (E p).metricExtension (E p).frameExtension z.1 z.2 =
    unitChartBase J α hs ht p.val uv.1 at he2
  have hus := angularChartCoordinates_source A J α hs ht E p huv
  have hq := (E p).centers_actual hzn.1
  have hy := ((E p).tube hzn).2
  rw [he1] at hq
  change normalMap (E p).metricExtension (E p).frameExtension z.1 z.2 ∈ (E p).actualDomain at hy
  rw [he2] at hy
  have hynK : unitChartBase J α hs ht p.val uv.1 ∈ K :=
    ⟨angularChartCoordinates A J α hs ht p uv,angularChartCoordinates_mem A J α hs ht E p huv,rfl⟩
  have huK : uv.1 ∈ unitChartDomain J α hs ht p.val K := by
    refine ⟨unitChartBase J α hs ht p.val uv.1,hynK,?_⟩
    exact (extChartAt Model p.val).left_inv hus.2
  have ham := (harea uv.1 huK).1
  let a := unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val uv.1) uv.1
  let b := unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val uv.2) uv.2
  let T := exteriorTransform ((E p).frameExtension (unitChartBase J α hs ht p.val uv.1))
  let S := exteriorTransform ((E p).frameExtension (unitChartBase J α hs ht p.val uv.2))
  have han : m ≤ ‖T a‖ := by
    rw [unitCoordinate_exterior_norm A J α hs ht E hE p uv.1 hus.2 hy]
    exact ham
  have hbn : S b ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [unitCoordinate_exterior_norm A J α hs ht E hE p uv.2 hus.1 hq]
    exact ne_of_gt (unitChartPlane J α hs ht p.val uv.2 hus.1).2.2.2
  have hbu : ‖b‖ = 1 := by
    obtain ⟨v,hv,hvb⟩ := unitCoordinate_line A J α hs ht E hE p ((E p).actual_subset hq) uv.2
      ((extChartAt Model p.val).left_inv hus.1)
    change ‖unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val uv.2) uv.2‖ = 1
    rw [hvb]
    exact unit_line_norm hv
  have hd := euclidean_transport_difference J α ht p.val (E p).chart
    (E p).metricExtension (E p).frameExtension hlin hzn.1 hz a b hbu
  rw [he2,he1] at hd
  have hAB : ‖T a-S b‖ ≤ ‖T‖*normalAngular A J α hs ht E p z uv.1 uv.2 + L*‖z.2‖ := by
    dsimp only [normalAngular]
    rw [he2]
    have hez : z = (unitChartBase J α hs ht p.val uv.2,z.2) := Prod.ext he1 rfl
    rw [hez]
    exact hd
  have hnorm : ‖T‖ ≤ max (max B 0) L :=
    (hB _ hynK).trans ((le_max_left B 0).trans (le_max_left _ _))
  have ha0 : 0 ≤ normalAngular A J α hs ht E p z uv.1 uv.2 := norm_nonneg _
  have hlf := first_lipschitz_bound hm han hbn
  rw [unitCoordinate_exterior_first A J α hs ht E hE p uv.1 hus.2 hy,
    unitCoordinate_exterior_first A J α hs ht E hE p uv.2 hus.1 hq] at hlf
  apply hlf.trans
  apply (mul_le_mul_of_nonneg_left hAB (by positivity : 0 ≤ 2/m)).trans
  change (2/m)*(‖T‖*_+L*‖z.2‖) ≤ C*(_+‖z.2‖)
  dsimp only [C]
  calc
    _ ≤ (2/m)*(max (max B 0) L*normalAngular A J α hs ht E p z uv.1 uv.2+
        max (max B 0) L*‖z.2‖) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right hnorm ha0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))) (by positivity)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
