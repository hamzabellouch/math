import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationQBound
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationVariationBound
import OAI.Geometry.TamingCompatibility.DifferentialForms.SecondPlaneVariation

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Hermitian Concentration PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [ConnectedSpace X] [SecondCountableTopology X] in
lemma concentration_first_estimate
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (p : A.centers) {r : ℝ} (hr : 0 < r) (x : X) (hx : x ∈ tsupport (A.partition p)) (w v : Space) :
    |fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x) w| ≤
      |⟪Q,smoothL2 A J α hs ht true (concentrationTest A J α ht E hE p r hr x hx v)⟫| +
      ∫ u, (unitChartDomain J α hs ht p.val (E p).concentrationCompact).indicator
        (fun u => unitChartArea J α hs ht p.val u *
          |fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
            (extChartAt Model p.val x-unitChartBase J α hs ht p.val u)
            (w-skew (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u) v)|) u ∂μ := by
  let k := cutKernel (E p).concentrationCutoff.bump r
  let b := extChartAt Model p.val x
  let S := unitChartDomain J α hs ht p.val (E p).concentrationCompact
  let t := fun u => fderiv ℝ k (b-unitChartBase J α hs ht p.val u)
    (w-skew (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u) v)
  have hk := cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff
  have htc : ContinuousOn t S :=
    ((hk.continuous_fderiv (by simp)).comp_continuousOn
      (continuousOn_const.sub (unitChartBase_continuousOn J α hs ht p.val (E p).concentrationCompact_target))).clm_apply
      (continuousOn_const.sub (unitChartSkew_continuousOn J α hs ht p.val v (E p).concentrationCompact_target))
  have hi := planeWeighted_integrable J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ (fun u => |t u|) htc.abs
  simp only [smul_eq_mul] at hi
  have hnorm : |∫ u, S.indicator (fun u => unitChartArea J α hs ht p.val u*t u) u ∂μ| ≤
      ∫ u, S.indicator (fun u => unitChartArea J α hs ht p.val u*|t u|) u ∂μ := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hi
    apply ae_of_all
    intro u
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu,indicator_of_mem hu,Real.norm_eq_abs,abs_mul,
        abs_of_nonneg (show 0 ≤ unitChartArea J α hs ht p.val u from by exact mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    · rw [indicator_of_notMem hu,indicator_of_notMem hu,norm_zero]
  have hid := planeConvolution_first_variation J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target μ k hk
    (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r) b w v
    ((E p).concentrationCutoff.reflected_support (partition_center_ball A J α ht E hE p hx) r)
  have ht0 := hT (concentrationTest A J α ht E hE p r hr x hx v)
    (concentrationTest_closed A J α ht E hE p hr x hx v)
  change fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x) w +
    unitMeasureCurrent J (hermitianMetric J α hs ht) μ (concentrationTest A J α ht E hE p r hr x hx v) = _ at hid
  have hd : fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x) w =
      ⟪Q,smoothL2 A J α hs ht true (concentrationTest A J α ht E hE p r hr x hx v)⟫ +
      ∫ u, S.indicator (fun u => unitChartArea J α hs ht p.val u*t u) u ∂μ := by linarith
  rw [hd]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hnorm)

omit [SecondCountableTopology X] in
include hE in
lemma concentration_plane_estimate
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (p : A.centers) :
    ∃ B C L : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 < L ∧ ∀ r : ℝ, 0 < r →
      ∀ u : MetricUnit (hermitianMetric J α hs ht),
      A.partition p u.val.proj *
        (|fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartFirst J α hs ht p.val u)|+
         |fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)|) ≤
      B*physicalQError A J α hs ht (l2Coefficients A J α hs ht E hE Q) L r u.val.proj+C*r^4 +
      (∫ v, variationDensity A J α hs ht E p r (v,u) ∂μ)+
      (∫ v, secondVariationDensity A J α hs ht E p r (v,u) ∂μ) := by
  obtain ⟨B,C,L,hB,hC,hL,hq⟩ := concentrationTest_Q_bound A J α hs ht E hE Q p
  refine ⟨2*B,2*C,L,by positivity,by positivity,hL,fun r hr u => ?_⟩
  have hn : 0 ≤ B*physicalQError A J α hs ht (l2Coefficients A J α hs ht E hE Q) L r u.val.proj+C*r^4 :=
    add_nonneg (mul_nonneg hB (physicalQError_nonneg A J α hs ht _ hr _)) (by positivity)
  by_cases hz : A.partition p u.val.proj = 0
  · simp only [hz,zero_mul,variationDensity,secondVariationDensity,integral_zero,add_zero]
    nlinarith
  have hx : u.val.proj ∈ tsupport (A.partition p) := subset_tsupport _ hz
  have hu := unitChartPlane J α hs ht p.val u (A.subordinate p hx)
  have hfirst := concentration_first_estimate A J α hs ht E hE μ Q hT p hr u.val.proj hx
    (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)
  have hsecond := concentration_first_estimate A J α hs ht E hE μ Q hT p hr u.val.proj hx
    (unitChartSecond J α hs ht p.val u) (-unitChartFirst J α hs ht p.val u)
  have hq1 := hq r hr u.val.proj hx (unitChartSecond J α hs ht p.val u)
  have hq2 := hq r hr u.val.proj hx (-unitChartFirst J α hs ht p.val u)
  rw [hu.2.1,mul_one] at hq1
  rw [norm_neg,hu.1,mul_one] at hq2
  have hf := mul_le_mul_of_nonneg_left (hfirst.trans (add_le_add hq1 le_rfl)) (A.partition.nonneg p u.val.proj)
  have hg := mul_le_mul_of_nonneg_left (hsecond.trans (add_le_add hq2 le_rfl)) (A.partition.nonneg p u.val.proj)
  simp only [mul_add,← integral_const_mul] at hf hg
  change _ ≤ _ + (∫ v, variationDensity A J α hs ht E p r (v,u) ∂μ) at hf
  change _ ≤ _ + (∫ v, secondVariationDensity A J α hs ht E p r (v,u) ∂μ) at hg
  have hp := mul_le_of_le_one_left hn (A.partition.le_one p u.val.proj)
  dsimp only [unitChartBase] at hf hg ⊢
  nlinarith
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
