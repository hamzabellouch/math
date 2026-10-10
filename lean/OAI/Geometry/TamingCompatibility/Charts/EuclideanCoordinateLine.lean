import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.EuclideanUnitPlanes
import OAI.Geometry.TamingCompatibility.Hodge.HodgeActualAngular
import OAI.Geometry.TamingCompatibility.DifferentialForms.WedgeTransform

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
lemma unitChart_eval_raw (p : X) (β : TwoForm X)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    ManifoldForms.pullback β (extChartAt Model p).symm (unitChartBase J α hs ht p u)
      ![unitChartVector J α hs ht p u,unitChartJVector J α hs ht p u] =
      eval β u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  let t := trivializationAt Space (TangentSpace Model) p
  have hb : u.val.proj ∈ t.baseSet := by
    simpa only [t,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hu
  have hv : t.symmL ℝ u.val.proj (unitChartVector J α hs ht p u) = u.val.2 := by
    change t.symmL ℝ u.val.proj ((t u.val).2) = _
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hb]
    exact t.symmL_continuousLinearMapAt hb _
  dsimp only [unitChartJVector,unitChartBase]
  rw [pullback_complexLine J β p ((extChartAt Model p).map_source hu),
    inverseChart_derivative p ((extChartAt Model p).map_source hu)]
  change eval β ((extChartAt Model p).symm (extChartAt Model p u.val.proj))
    (t.symmL ℝ ((extChartAt Model p).symm (extChartAt Model p u.val.proj)) _)
    (J.endomorphism _ (t.symmL ℝ ((extChartAt Model p).symm (extChartAt Model p u.val.proj)) _)) = _
  rw [(extChartAt Model p).left_inv hu,hv]
end TamingCompatibility.GeometricHilbert.Hermitian

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

include hE in
lemma unitCoordinate_rawVector (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht)) (hu : (extChartAt Model p.val).symm q = u.val.proj) :
    unitCoordinate A J α hs ht E p q u = HodgeChart.rawVector J α ht p.val (E p).chart
      (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val q := by
  unfold unitCoordinate
  rw [← unitDual_encode A J α hs ht E hE,← hu,
    ← coordinateEncode_rawVector J α ht A E p _ hq,coordinateDecode_encode J α ht A E hE p hq]

include hE in
lemma unitCoordinate_directionCoordinates (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).chart.domain) :
    unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u =
      line (directionCoordinates (coordinateMetric J α ht p.val
        (unitChartBase J α hs ht p.val u)) (by simp [Space])
        (fun i => (E p).chart.frame i (unitChartBase J α hs ht p.val u))
        ((E p).chart.frame_gram _ hq) (unitChartVector J α hs ht p.val u)) := by
  let q := unitChartBase J α hs ht p.val u
  have he : (extChartAt Model p.val).symm q = u.val.proj := (extChartAt Model p.val).left_inv hu
  rw [unitCoordinate_rawVector A J α hs ht E hE p hq u he]
  apply ext_inner_right ℝ
  intro w
  let β := HodgeChart.manifoldTest J α ht p.val (E p).chart (fun _ => w)
  have hβ : HodgeChart.rawVector J α ht p.val (E p).chart β q = w :=
    rawVector_constant_test J α ht p.val (E p).chart hq w
  rw [← hβ,rawVector_pairing J α ht p.val (E p).chart hq,he,
    unitDual_pairing A J α hs ht E hE (hermitianMetric J α hs ht) β u,
    ← unitChart_eval_raw J α hs ht p.val β u hu,real_inner_comm]
  obtain ⟨h0,h1,h2,h3⟩ := (E p).chart.frame_complex q hq
  exact coordinates_direction_eval _ _ _ ((E p).chart.frame_gram q hq)
    (coordinateJ J p.val q) h0 h1 h2 h3 _ _

include hE in
lemma unitCoordinate_wedgeTransform (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).chart.domain) :
    wedgeTransform (fun i => (E p).chart.frame i (unitChartBase J α hs ht p.val u))
      (unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u) =
      wedge (unitChartVector J α hs ht p.val u) (unitChartJVector J α hs ht p.val u) := by
  rw [unitCoordinate_directionCoordinates A J α hs ht E hE p u hu hq,line,wedgeTransform_wedge]
  have hv := sum_directionCoordinates (coordinateMetric J α ht p.val
    (unitChartBase J α hs ht p.val u)) (by simp [Space]) _ ((E p).chart.frame_gram _ hq)
    (unitChartVector J α hs ht p.val u)
  obtain ⟨h0,h1,h2,h3⟩ := (E p).chart.frame_complex _ hq
  rw [← complex_frame_sum _ _ h0 h1 h2 h3,hv]
  rfl

include hE in
lemma unitCoordinate_normalized_wedgeTransform (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).chart.domain) :
    PlaneVariation.first (wedgeTransform (fun i => (E p).chart.frame i (unitChartBase J α hs ht p.val u))
      (unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u)) =
      wedge (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u) := by
  rw [unitCoordinate_wedgeTransform A J α hs ht E hE p u hu hq]
  have ha := unitChartVector_ne_zero J α hs ht p.val u hu
  have hab := normalPart_complex_ne_zero (coordinateJ J p.val
    (unitChartBase J α hs ht p.val u))
    (coordinateJ_square J p.val ((extChartAt Model p.val).map_source hu)) ha
  rw [show unitChartFirst J α hs ht p.val u = PlaneVariation.first (unitChartVector J α hs ht p.val u) from rfl,
    show unitChartSecond J α hs ht p.val u = PlaneVariation.second (unitChartVector J α hs ht p.val u)
      (unitChartJVector J α hs ht p.val u) from rfl,wedge_normalized _ _ ha]
  change ‖wedge _ _‖⁻¹ • wedge _ _ = _
  dsimp only [unitChartJVector]
  rw [norm_wedge_area _ _ ha hab]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.UnitaryFrame
open scoped ContDiff

def exteriorTransform (B : V →L[ℝ] V) : W →L[ℝ] W :=
  wedgeTransform (fun i => B (EuclideanSpace.single i 1))

lemma exteriorTransform_smooth {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {B : D → V →L[ℝ] V} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun q => exteriorTransform (B q)) :=
  wedgeTransform_contDiff (fun _i => hB.clm_apply contDiff_const)

lemma exteriorTransform_frame (b : Fin 4 → V) :
    exteriorTransform (GeometricHilbert.GeometricNormalCharts.frameMap b) = wedgeTransform b := by
  unfold exteriorTransform
  congr 1
  funext i
  simp [GeometricHilbert.GeometricNormalCharts.frameMap_apply]
end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma euclidean_transport_linear (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
      ‖(exteriorTransform (B (normalMap g B q z))).comp (normalGauge J α ht p D g B (q,z)) -
        exteriorTransform (B q)‖ ≤ C*‖z‖ := by
  let F : Space × Space → W →L[ℝ] W := fun x =>
    (exteriorTransform (B (normalMap g B x.1 x.2))).comp (normalGauge J α ht p D g B x)
  let Ω : Set (Space × Space) := (fun x : Space × Space => (x.1,(0 : Space))) ⁻¹' normalDomain J α ht p D g B
  have hΩ : IsOpen Ω := (normalDomain_open J α ht p D g B hg hB).preimage
    (continuous_fst.prodMk continuous_const)
  have hKΩ : K ×ˢ {(0 : Space)} ⊆ Ω := by
    rintro ⟨q,z⟩ ⟨hq,_⟩
    exact ((hactual q hq).center J α ht p D g B).1
  have hF : ∀ x ∈ Ω, ContDiffAt ℝ ∞ F x := fun x hx =>
    ((exteriorTransform_smooth hB).comp (normalMap_joint g B hg hB)).contDiffAt.clm_comp
      (normalGauge_smooth J α ht p D g B hs hg hB hx)
  obtain ⟨C,hC,r,hr,_,hb⟩ := local_linear_bound F K hK Ω hΩ hKΩ hF
  refine ⟨C,hC,r,hr,fun q hq z hz => ?_⟩
  simpa only [F,normalMap_zero,normalGauge_zero,ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id] using hb q hq z hz

lemma euclidean_transport_difference {K : Set Space} {C r : ℝ}
    (hC : ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
      ‖(exteriorTransform (B (normalMap g B q z))).comp (normalGauge J α ht p D g B (q,z)) -
        exteriorTransform (B q)‖ ≤ C*‖z‖)
    {q : Space} (hq : q ∈ K) {z : Space} (hz : ‖z‖ ≤ r) (a b : W) (hb : ‖b‖ = 1) :
    ‖exteriorTransform (B (normalMap g B q z)) a - exteriorTransform (B q) b‖ ≤
      ‖exteriorTransform (B (normalMap g B q z))‖ *
        ‖a-normalGauge J α ht p D g B (q,z) b‖ + C*‖z‖ := by
  let T := exteriorTransform (B (normalMap g B q z))
  let U := normalGauge J α ht p D g B (q,z)
  let S := exteriorTransform (B q)
  have he : T a-S b = T (a-U b)+(T.comp U-S) b := by simp only [map_sub,sub_apply,ContinuousLinearMap.comp_apply]; abel
  calc
    _ ≤ ‖T (a-U b)‖+‖(T.comp U-S) b‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ ‖T‖*‖a-U b‖+‖T.comp U-S‖*‖b‖ := add_le_add (T.le_opNorm _) ((T.comp U-S).le_opNorm _)
    _ ≤ _ := by rw [hb,mul_one]; exact add_le_add le_rfl (hC q hq z hz)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
