import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SecondPlaneVariation

namespace OAI

section

noncomputable section
namespace TamingCompatibility.PlaneVariation
open Set
open scoped RealInnerProductSpace
lemma continuousOn_secondVariation {Y V : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f g : Y → V} {S : Set Y} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
    ContinuousOn (fun uv : Y × Y => g uv.2-skew (f uv.1) (g uv.1) (-f uv.2)) (S ×ˢ S) := by
  have hf1 : ContinuousOn (fun uv : Y × Y => f uv.1) (S ×ˢ S) := hf.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hf2 : ContinuousOn (fun uv : Y × Y => f uv.2) (S ×ˢ S) := hf.comp continuous_snd.continuousOn (fun _ h => h.2)
  have hg1 : ContinuousOn (fun uv : Y × Y => g uv.1) (S ×ˢ S) := hg.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hg2 : ContinuousOn (fun uv : Y × Y => g uv.2) (S ×ˢ S) := hg.comp continuous_snd.continuousOn (fun _ h => h.2)
  exact hg2.sub (((hg1.inner hf2.neg).smul hf1).sub ((hf1.inner hf2.neg).smul hg1))
end TamingCompatibility.PlaneVariation
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def secondVariationRaw (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) : ℝ :=
  A.partition p uv.2.val.proj * (unitChartArea J α hs ht p.val uv.1 *
    |fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
      (unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1)
      (unitChartSecond J α hs ht p.val uv.2-
        skew (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1)
          (-unitChartFirst J α hs ht p.val uv.2))|)

include hE in
omit [T2Space X] [CompactSpace X] [SecondCountableTopology X] in
lemma secondVariationDensity_eq_indicator (p : A.centers) (r : ℝ) :
    secondVariationDensity A J α hs ht E p r =
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)).indicator
        (secondVariationRaw A J α hs ht E p r) := by
  funext uv
  by_cases hu : uv.1 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · by_cases hv : uv.2 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
    · simp only [secondVariationDensity,indicator_of_mem hu,indicator_of_mem (show uv ∈ _ ×ˢ _ from ⟨hu,hv⟩),secondVariationRaw]
    · have hz : A.partition p uv.2.val.proj = 0 := by
        by_contra hn
        have hc := partition_center_ball A J α ht E hE p (subset_tsupport _ hn)
        have hsrc := (E p).source_subset (hE p (subset_tsupport _ hn))
        exact hv ⟨_,(E p).concentrationCompact_center hc,(extChartAt Model p.val).left_inv hsrc⟩
      simp only [secondVariationDensity,indicator_of_mem hu,hz,zero_mul,
        indicator_of_notMem (show uv ∉ _ ×ˢ _ from fun h => hv h.2)]
  · simp only [secondVariationDensity,indicator_of_notMem hu,mul_zero,
      indicator_of_notMem (show uv ∉ _ ×ˢ _ from fun h => hu h.1)]

def secondVariationVector (p : A.centers) (uv : UnitPair J α hs ht) : Space :=
  unitChartSecond J α hs ht p.val uv.2-
    skew (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1)
      (-unitChartFirst J α hs ht p.val uv.2)

omit [CompactSpace X] [SecondCountableTopology X] [T2Space X] in
lemma secondVariationVector_continuousOn (p : A.centers) :
    ContinuousOn (secondVariationVector A J α hs ht p)
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)) := by
  exact PlaneVariation.continuousOn_secondVariation
    (unitChartFirst_continuousOn J α hs ht p.val (E p).concentrationCompact_target)
    (unitChartSecond_continuousOn J α hs ht p.val (E p).concentrationCompact_target)

omit [CompactSpace X] [SecondCountableTopology X] [T2Space X] in
lemma secondVariationRaw_continuousOn (p : A.centers) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (secondVariationRaw A J α hs ht E p r)
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)) := by
  let S := unitChartDomain J α hs ht p.val (E p).concentrationCompact
  have hb := unitChartBase_continuousOn J α hs ht p.val (E p).concentrationCompact_target
  have hz : ContinuousOn (fun uv : UnitPair J α hs ht =>
      unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1) (S ×ˢ S) :=
    (hb.comp continuous_snd.continuousOn (fun _ h => h.2)).sub (hb.comp continuous_fst.continuousOn (fun _ h => h.1))
  have hd := ((cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff).continuous_fderiv (by simp)).comp_continuousOn hz
  have ha : ContinuousOn (fun uv : UnitPair J α hs ht => unitChartArea J α hs ht p.val uv.1) (S ×ˢ S) := (unitChartArea_continuousOn J α hs ht p.val (E p).concentrationCompact_target).comp continuous_fst.continuousOn (fun _ h => h.1)
  have hp : ContinuousOn (fun uv : UnitPair J α hs ht => A.partition p uv.2.val.proj) (S ×ˢ S) :=
    ((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).fst).continuousOn
  exact hp.mul (ha.mul (hd.clm_apply (secondVariationVector_continuousOn A J α hs ht E p)).abs)

include hE in
lemma secondVariationDensity_integrable (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    [IsFiniteMeasure μ] (p : A.centers) {r : ℝ} (hr : 0 < r) :
    Integrable (secondVariationDensity A J α hs ht E p r) (μ.prod μ) := by
  classical
  let S := (unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)
  have hc := unitChartDomain_closed J α hs ht p.val (E p).concentrationCompact_compact (E p).concentrationCompact_target
  have hS : _root_.IsClosed S := hc.prod hc
  have hf := secondVariationRaw_continuousOn A J α hs ht E p hr
  have hm := hf.measurable_piecewise
    (continuousOn_const : ContinuousOn (fun _ : UnitPair J α hs ht => (0 : ℝ)) Sᶜ) hS.measurableSet
  have hm' : Measurable (secondVariationDensity A J α hs ht E p r) := by
    convert hm using 1
    funext uv
    rw [secondVariationDensity_eq_indicator A J α hs ht E hE p r]
    by_cases huv : uv ∈ S <;> simp [Set.indicator, Set.piecewise, S] at huv ⊢
  obtain ⟨C,hC⟩ := hS.isCompact.exists_bound_of_continuousOn hf
  apply (integrable_const (max C 0 : ℝ)).mono' hm'.aestronglyMeasurable
  apply ae_of_all
  intro uv
  rw [secondVariationDensity_eq_indicator A J α hs ht E hE p r]
  by_cases huv : uv ∈ S
  · rw [indicator_of_mem huv]
    exact (hC uv huv).trans (le_max_left _ _)
  · rw [indicator_of_notMem huv,norm_zero]
    exact le_max_right _ _
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
