import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationChart
import OAI.Geometry.TamingCompatibility.DifferentialForms.EuclideanAngularRadial
import OAI.Geometry.TamingCompatibility.DifferentialForms.UnitTransversePair
import OAI.Geometry.TamingCompatibility.DifferentialForms.PlaneFirstVariation

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.Concentration
open PlaneVariation UnitaryFrame
lemma wedge_second_neg_first (u v : V) : wedge v (-u) = wedge u v := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma cutKernel_plane_second_variation_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    {a : ℝ} (ha : 0 < a) (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u v b c z : V,
      ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      ‖b‖ = 1 → ‖c‖ = 1 → inner ℝ b c = 0 →
      |fderiv ℝ (cutKernel η r) z (v-skew b c (-u))| ≤
        15*radialCoefficient r ‖z‖*‖wedge u v-wedge b c‖^2*‖z‖ +
        6*radialCoefficient r ‖z‖*‖wedge u v-wedge b c‖*‖transverse b c z‖ + C*r^4 := by
  obtain ⟨C,hC,hbound⟩ := cutKernel_plane_variation_bound η hη hηc hη0 hη1 ha hηone
  refine ⟨C,hC,fun r hr u v b c z hu hv huv hb hc hbc => ?_⟩
  have h := hbound r hr v (-u) b c z hv (by simpa only [norm_neg] using hu)
    (by rw [inner_neg_right,real_inner_comm,huv,neg_zero]) hb hc hbc
  rwa [wedge_second_neg_first] at h
end TamingCompatibility.Concentration

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def secondVariationDensity (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) : ℝ :=
  A.partition p uv.2.val.proj *
    (unitChartDomain J α hs ht p.val (E p).concentrationCompact).indicator
      (fun u => unitChartArea J α hs ht p.val u *
        |fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
          (unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val u)
          (unitChartSecond J α hs ht p.val uv.2-
            skew (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)
              (-unitChartFirst J α hs ht p.val uv.2))|) uv.1

omit [T2Space X] [CompactSpace X] in
lemma secondVariationDensity_nonneg (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) :
    0 ≤ secondVariationDensity A J α hs ht E p r uv := by
  apply mul_nonneg (A.partition.nonneg _ _)
  apply indicator_nonneg _ uv.1
  intro u _
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)

include hE in
lemma secondVariationDensity_bound (p : A.centers) :
    ∃ P C : ℝ, 0 ≤ P ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ uv : UnitPair J α hs ht,
      secondVariationDensity A J α hs ht E p r uv ≤
        15*P*(euclideanAngularGlobal A J α hs ht E p uv *
          radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)*
            euclideanDistanceGlobal A J α hs ht E p uv) +
        6*P*(Real.sqrt (euclideanAngularGlobal A J α hs ht E p uv *
          radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv))*
          Real.sqrt (transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap)) + C*r^4 := by
  obtain ⟨_,P,_,hP,harea⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  have hone : ∀ z : Space, ‖z‖ < (E p).concentrationCutoff.radius/2 → (E p).concentrationCutoff.bump z = 1 := by
    intro z hz
    apply ContDiffBump.one_of_mem_closedBall
    change dist z 0 ≤ (E p).concentrationCutoff.radius/2
    simpa only [dist_zero_right] using hz.le
  obtain ⟨C,hC,hder⟩ := cutKernel_plane_second_variation_bound
    (E p).concentrationCutoff.bump (E p).concentrationCutoff.bump.contDiff
    (E p).concentrationCutoff.bump.hasCompactSupport
    (fun z => (E p).concentrationCutoff.bump.nonneg (x := z))
    (fun z => (E p).concentrationCutoff.bump.le_one (x := z))
    (by linarith [(E p).concentrationCutoff.positive] : 0 < (E p).concentrationCutoff.radius/2) hone
  refine ⟨P,P*C,hP.le,by positivity,fun r hr uv => ?_⟩
  have hright : 0 ≤ 15*P*(euclideanAngularGlobal A J α hs ht E p uv *
          radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)*
            euclideanDistanceGlobal A J α hs ht E p uv) +
        6*P*(Real.sqrt (euclideanAngularGlobal A J α hs ht E p uv *
          radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv))*
          Real.sqrt (transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap)) + (P*C)*r^4 := by
    have := euclideanAngularGlobal_nonneg A J α hs ht E p uv
    have := euclideanDistanceGlobal_nonneg A J α hs ht E p uv
    have := radialCoefficient_nonneg r (euclideanDistanceGlobal A J α hs ht E p uv)
    positivity
  by_cases hc : A.partition p uv.2.val.proj = 0
  · rw [secondVariationDensity,hc,zero_mul]
    exact hright
  have hx : uv.2.val.proj ∈ tsupport (A.partition p) := subset_tsupport _ (Function.mem_support.mpr hc)
  have hcenter := partition_center_ball A J α ht E hE p hx
  have hcentersrc := A.subordinate p hx
  have hvK : uv.2 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact :=
    ⟨unitChartBase J α hs ht p.val uv.2,(E p).concentrationCompact_center hcenter,
      (extChartAt Model p.val).left_inv hcentersrc⟩
  by_cases hu : uv.1 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  swap
  · rw [secondVariationDensity,indicator_of_notMem hu,mul_zero]
    exact hright
  let z := unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1
  by_cases hz : z ∈ tsupport ((E p).concentrationCutoff.bump : Space → ℝ)
  swap
  · have hzero : fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r) z = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun hz' => hz (cutKernel_tsupport _ _ hz'))
    rw [secondVariationDensity,indicator_of_mem hu]
    change A.partition p uv.2.val.proj*(unitChartArea J α hs ht p.val uv.1*|fderiv ℝ _ z _|) ≤ _
    rw [hzero,zero_apply,abs_zero,mul_zero,mul_zero]
    exact hright
  have husrc := (unitChart_mem J α hs ht p.val (E p).concentrationCompact_target hu).1
  have hn : ‖unitChartBase J α hs ht p.val uv.1-unitChartBase J α hs ht p.val uv.2‖ ≤
      (E p).concentrationCutoff.radius := by
    rw [(E p).concentrationCutoff.bump.tsupport_eq] at hz
    change dist z 0 ≤ _ at hz
    simpa only [dist_zero_right,z,norm_sub_rev,ParametrixData.ConcentrationCutoff.bump] using hz
  have hphys := (E p).concentrationCutoff.near _ hcenter _ hn
  have hang : uv ∈ angularDomain A J α hs ht E p := by
    refine ⟨(unitChartBase J α hs ht p.val uv.2,unitChartBase J α hs ht p.val uv.1),hphys,?_⟩
    exact Prod.ext ((extChartAt Model p.val).left_inv hcentersrc) ((extChartAt Model p.val).left_inv husrc)
  obtain ⟨hu1,hu2,hu3,_⟩ := unitChartPlane J α hs ht p.val uv.1 husrc
  obtain ⟨hv1,hv2,hv3,_⟩ := unitChartPlane J α hs ht p.val uv.2 hcentersrc
  have hd := hder r hr _ _ _ _ z hv1 hv2 hv3 hu1 hu2 hu3
  have hpbound : secondVariationDensity A J α hs ht E p r uv ≤
      A.partition p uv.2.val.proj * P *
        (15*radialCoefficient r ‖z‖*‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2*‖z‖+
          6*radialCoefficient r ‖z‖*‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖*
            ‖transverse (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1) z‖+C*r^4) := by
    rw [secondVariationDensity,indicator_of_mem hu,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (A.partition.nonneg _ _)
    apply mul_le_mul (harea uv.1 hu).2 _ (abs_nonneg _) hP.le
    simpa only [euclideanLine,norm_sub_rev] using hd
  have htnorm : ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.2) uv.1‖ =
      ‖transverse (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1) z‖ := by
    unfold unitTransverse
    rw [show unitChartBase J α hs ht p.val uv.1-unitChartBase J α hs ht p.val uv.2 = (-1:ℝ) • z by simp [z],
      transverse_smul,norm_smul,Real.norm_eq_abs,abs_neg,abs_one,one_mul]
  have hrad : euclideanDistanceGlobal A J α hs ht E p uv = ‖z‖ := by
    simp only [euclideanDistanceGlobal,indicator_of_mem hang,angularChartCoordinates,z,unitChartBase,norm_sub_rev]
  have hweight : euclideanAngularGlobal A J α hs ht E p uv =
      A.partition p uv.2.val.proj*‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2 :=
    indicator_of_mem hang _
  have htrans : transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap =
      A.partition p uv.2.val.proj*radialCoefficient r ‖z‖*
        ‖transverse (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1) z‖^2 := by
    rw [transversePairKernel,indicator_of_mem (show uv.swap ∈ _ ×ˢ _ from ⟨hvK,hu⟩)]
    simp only [Prod.swap,htnorm,z,norm_sub_rev]
  rw [hweight,hrad,htrans,sqrt_angular_transverse (A.partition.nonneg _ _) (radialCoefficient_nonneg _ _) (norm_nonneg _) (norm_nonneg _)]
  have hrem := mul_le_mul_of_nonneg_right (A.partition.le_one p uv.2.val.proj)
    (by positivity : 0 ≤ P*C*r^4)
  nlinarith [hpbound]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
