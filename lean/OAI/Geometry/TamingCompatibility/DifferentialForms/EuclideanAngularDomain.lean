import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.EuclideanAngularPoint
import OAI.Geometry.TamingCompatibility.Hodge.HodgeWedgeMassUpper

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)

def euclideanNearSet (s : ℝ) (p : A.centers) : Set (UnitPair J α hs ht) :=
  angularDomain A J α hs ht E p ∩
    {uv | ‖(angularChartCoordinates A J α hs ht p uv).2-
      (angularChartCoordinates A J α hs ht p uv).1‖ ≤ s}

omit [CompactSpace X] in
lemma euclideanNearSet_closed (s : ℝ) (p : A.centers) :
    _root_.IsClosed (euclideanNearSet A J α hs ht E s p) :=
  ((angularChartCoordinates_continuousOn A J α hs ht E p).snd.sub
    (angularChartCoordinates_continuousOn A J α hs ht E p).fst).norm.preimage_isClosed_of_isClosed
      (angularDomain_closed A J α hs ht E p) isClosed_Iic

omit [CompactSpace X] [T2Space X] in
lemma euclideanLine_continuousOn (p : A.centers) :
    ContinuousOn (fun uv : UnitPair J α hs ht =>
      euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2)
      (angularDomain A J α hs ht E p) := by
  let K := Prod.fst '' (E p).physicalCompact ∪ Prod.snd '' (E p).physicalCompact
  have hKt : K ⊆ (extChartAt Model p.val).target := by
    rintro y (⟨xy,hxy,rfl⟩ | ⟨xy,hxy,rfl⟩)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).1)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).2)
  have hb : ContinuousOn (fun u : MetricUnit (hermitianMetric J α hs ht) =>
      euclideanLine A J α hs ht p u) (unitChartDomain J α hs ht p.val K) := by
    intro u hu
    have hsrc := (unitChart_mem J α hs ht p.val hKt hu).1
    have hn := unitChartVector_ne_zero J α hs ht p.val u hsrc
    have hn' := normalPart_complex_ne_zero _
      (coordinateJ_square J p.val ((extChartAt Model p.val).map_source hsrc)) hn
    have h1 := (unitChartVector_continuousOn J α hs ht p.val hKt u hu)
    have h2 := (unitChartJVector_continuousOn J α hs ht p.val hKt u hu)
    have hf := (first_continuousAt hn).comp_continuousWithinAt h1
    have hsc : ContinuousAt (fun v : Space × Space => second v.1 v.2)
        (unitChartVector J α hs ht p.val u,unitChartJVector J α hs ht p.val u) := second_continuousAt hn hn'
    have hg := ContinuousAt.comp_continuousWithinAt (x := u)
      (g := fun v : Space × Space => second v.1 v.2)
      (f := fun u => (unitChartVector J α hs ht p.val u,unitChartJVector J α hs ht p.val u)) hsc (h1.prodMk h2)
    have hw : Continuous (fun ab : Space × Space => wedge ab.1 ab.2) := by
      unfold wedge
      fun_prop
    exact ContinuousAt.comp_continuousWithinAt (x := u)
      (g := fun ab : Space × Space => wedge ab.1 ab.2)
      (f := fun v => (unitChartFirst J α hs ht p.val v,unitChartSecond J α hs ht p.val v))
      hw.continuousAt (hf.prodMk hg)
  have hf : MapsTo Prod.fst (angularDomain A J α hs ht E p) (unitChartDomain J α hs ht p.val K) := by
    intro uv huv
    have hxy := angularChartCoordinates_mem A J α hs ht E p huv
    have hsrc := (angularChartCoordinates_source A J α hs ht E p huv).2
    exact ⟨unitChartBase J α hs ht p.val uv.1,Or.inr ⟨_,hxy,rfl⟩,(extChartAt Model p.val).left_inv hsrc⟩
  have hg : MapsTo Prod.snd (angularDomain A J α hs ht E p) (unitChartDomain J α hs ht p.val K) := by
    intro uv huv
    have hxy := angularChartCoordinates_mem A J α hs ht E p huv
    have hsrc := (angularChartCoordinates_source A J α hs ht E p huv).1
    exact ⟨unitChartBase J α hs ht p.val uv.2,Or.inl ⟨_,hxy,rfl⟩,(extChartAt Model p.val).left_inv hsrc⟩
  exact (hb.comp continuous_fst.continuousOn hf).sub (hb.comp continuous_snd.continuousOn hg)

def euclideanAngularWeight (p : A.centers) (uv : UnitPair J α hs ht) : ℝ :=
  A.partition p uv.2.val.proj * ‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2

omit [CompactSpace X] [T2Space X] in
lemma euclideanAngularWeight_nonneg (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ euclideanAngularWeight A J α hs ht p uv :=
  mul_nonneg (A.partition.nonneg _ _) (sq_nonneg _)

omit [CompactSpace X] [T2Space X] in
lemma euclideanAngularWeight_continuousOn (p : A.centers) :
    ContinuousOn (euclideanAngularWeight A J α hs ht p) (angularDomain A J α hs ht E p) :=
  (((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).fst).continuousOn).mul
    ((euclideanLine_continuousOn A J α hs ht E p).norm.pow 2)

variable [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def euclideanAngularNear (s : ℝ) (p : A.centers) : UnitPair J α hs ht → ℝ :=
  (euclideanNearSet A J α hs ht E s p).indicator (euclideanAngularWeight A J α hs ht p)

omit [CompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma euclideanAngularNear_nonneg (s : ℝ) (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ euclideanAngularNear A J α hs ht E s p uv :=
  Set.indicator_nonneg (fun v _ => euclideanAngularWeight_nonneg A J α hs ht p v) uv

lemma euclideanAngularNear_integrable (s : ℝ) (p : A.centers)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    Integrable (euclideanAngularNear A J α hs ht E s p) (μ.prod μ) := by
  have hc := euclideanNearSet_closed A J α hs ht E s p
  apply (integrable_indicator_iff hc.measurableSet).mpr
  exact ContinuousOn.integrableOn_compact hc.isCompact
    ((euclideanAngularWeight_continuousOn A J α hs ht E p).mono inter_subset_left)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanNear_physical_distance (p : A.centers) :
    let := geometricMetricSpace J α hs ht
    ∃ L : ℝ, 0 < L ∧ ∀ s : ℝ, 0 < s → ∀ uv ∈ euclideanNearSet A J α hs ht E s p,
      dist uv.1.val.proj uv.2.val.proj ≤ L*s := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let K := Prod.fst '' (E p).physicalCompact ∪ Prod.snd '' (E p).physicalCompact
  have hK : IsCompact K := ((E p).physicalCompact_compact.image continuous_fst).union
    ((E p).physicalCompact_compact.image continuous_snd)
  have hKt : K ⊆ (extChartAt Model p.val).target := by
    rintro y (⟨xy,hxy,rfl⟩ | ⟨xy,hxy,rfl⟩)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).1)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).2)
  obtain ⟨C,hC⟩ := chartInverse_compact_lipschitz J α hs ht p.val K hK hKt
  refine ⟨(C:ℝ)+1,by positivity,fun s hs' uv huv => ?_⟩
  have hxy := angularChartCoordinates_mem A J α hs ht E p huv.1
  have hsrc := angularChartCoordinates_source A J α hs ht E p huv.1
  have hh := hC.dist_le_mul _ (show (angularChartCoordinates A J α hs ht p uv).2 ∈ K from Or.inr ⟨_,hxy,rfl⟩)
    _ (show (angularChartCoordinates A J α hs ht p uv).1 ∈ K from Or.inl ⟨_,hxy,rfl⟩)
  change dist ((extChartAt Model p.val).symm (extChartAt Model p.val uv.1.val.proj))
    ((extChartAt Model p.val).symm (extChartAt Model p.val uv.2.val.proj)) ≤ _ at hh
  rw [(extChartAt Model p.val).left_inv hsrc.2,(extChartAt Model p.val).left_inv hsrc.1,dist_eq_norm] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left huv.2 C.coe_nonneg).trans
    (mul_le_mul_of_nonneg_right (by linarith) hs'.le))

lemma separating_current_euclidean_near_mass
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s →
      (∫ uv, (euclideanNearSet A J α hs ht E s p).indicator (fun _ => (1:ℝ)) uv ∂μ.prod μ) ≤ C*s^2 := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨L,hL,hnear⟩ := euclideanNear_physical_distance A J α hs ht E p
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  refine ⟨512*M*L^2,by positivity,fun s hs' => ?_⟩
  let r := L*s
  have hr : 0 < r := mul_pos hL hs'
  let S := euclideanNearSet A J α hs ht E s p
  have hS : MeasurableSet S := (euclideanNearSet_closed A J α hs ht E s p).measurableSet
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (μ.prod μ) := (integrable_const _).indicator hS
  have hp := physicalProfile_integrable J α hs ht hr μ
  have hb (uv : UnitPair J α hs ht) :
      S.indicator (fun _ => (1:ℝ)) uv ≤ 64*((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6 := by
    by_cases huv : uv ∈ S
    · rw [indicator_of_mem huv]
      have hd := hnear s hs' uv huv
      have hdiv : dist uv.1.val.proj uv.2.val.proj/r ≤ 1 := (div_le_one hr).mpr hd
      have hpos : 0 < 1+dist uv.1.val.proj uv.2.val.proj/r := by positivity
      have hinv : (1/2:ℝ) ≤ (1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹ := by
        have hh : (1+dist uv.1.val.proj uv.2.val.proj/r) ≤ 2 := by linarith
        simpa only [one_div] using one_div_le_one_div_of_le hpos hh
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hinv 6
      norm_num only [div_pow,one_pow,show (2:ℝ)^6 = 64 by norm_num] at hh
      linarith
    · rw [indicator_of_notMem huv]
      positivity
  have hh := integral_mono hi (hp.const_mul 64) hb
  rw [integral_const_mul] at hh
  have hh' := mul_le_mul_of_nonneg_left
    (physicalProfile_integral_bound J α hs ht μ M hM hgrowth hr) (by norm_num : (0:ℝ)≤64)
  exact hh.trans (hh'.trans_eq (by dsimp [r]; ring))
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
