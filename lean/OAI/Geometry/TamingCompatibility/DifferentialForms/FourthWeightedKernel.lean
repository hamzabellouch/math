import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.CompactProfilePoint
import OAI.Geometry.TamingCompatibility.DifferentialForms.EuclideanAngularNearPoint

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace TamingCompatibility.FourthShell
open QuadraticShell
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

lemma weighted_profile_bound (w d : Y → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ y, 0 ≤ w y) (hd0 : ∀ y, 0 ≤ d y) (hwi : Integrable w μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s →
      (∫ y, {y | d y ≤ s}.indicator w y ∂μ) ≤ C*s^4)
    {r : ℝ} (hr : 0 < r) :
    (∫ y, w y*((1+d y/r)⁻¹)^6 ∂μ) ≤ 32*C*r^4 := by
  let ν := μ.withDensity (fun y => ENNReal.ofReal (w y))
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have hchange (f : Y → ℝ) : (∫ y, f y ∂ν) = ∫ y, w y*f y ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul (hw.ennreal_ofReal)
      (Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)) f]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by simp only [ENNReal.toReal_ofReal (hw0 y),smul_eq_mul])
  have hweight (S : Set Y) : (fun y => w y*S.indicator (fun _ => (1:ℝ)) y) = S.indicator w := by
    funext y
    by_cases hy : y ∈ S <;> simp [hy]
  have hν (S : Set Y) (hS : MeasurableSet S) : ν.real S = ∫ y, S.indicator w y ∂μ := by
    calc
      _ = ∫ y, S.indicator (fun _ => (1:ℝ)) y ∂ν := by simp [integral_indicator hS]
      _ = _ := by rw [hchange,hweight]
  let δ := fun y => ENNReal.ofReal (d y)
  have hδ : Measurable δ := hd.ennreal_ofReal
  have hg (s : ℝ) (hs : 0 < s) : ν.real {y | δ y < ENNReal.ofReal s} ≤ C*s^4 := by
    let S := {y | δ y < ENNReal.ofReal s}
    let T := {y | d y ≤ s}
    have hS : MeasurableSet S := measurableSet_lt hδ measurable_const
    have hT : MeasurableSet T := measurableSet_le hd measurable_const
    have hsub : S ⊆ T := by
      intro y hy
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff hs).mp hy)
    rw [hν S hS]
    apply (integral_mono (hwi.indicator hS) (hwi.indicator hT) ?_).trans (hgrowth s hs)
    intro y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy,indicator_of_mem (hsub hy)]
    · rw [indicator_of_notMem hy]
      exact Set.indicator_nonneg (fun z _ => hw0 z) y
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_profile_le ν δ hδ C hC hg hr)
  rw [ENNReal.toReal_ofReal (by positivity),← integral_profile_toReal ν δ hδ,hchange] at hh
  have he (y : Y) : (profile r (δ y)).toReal = ((1+d y/r)⁻¹)^6 := by
    rw [profile_ofReal hr (hd0 y),ENNReal.toReal_ofReal (by positivity)]
  simpa only [he] using hh
end TamingCompatibility.FourthShell

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
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def euclideanAngularGlobal (p : A.centers) : UnitPair J α hs ht → ℝ :=
  (angularDomain A J α hs ht E p).indicator (euclideanAngularWeight A J α hs ht p)

def euclideanDistanceGlobal (p : A.centers) : UnitPair J α hs ht → ℝ :=
  (angularDomain A J α hs ht E p).indicator
    (fun uv => ‖(angularChartCoordinates A J α hs ht p uv).2-(angularChartCoordinates A J α hs ht p uv).1‖)

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] [CompactSpace X] in
lemma euclideanAngularGlobal_measurable (p : A.centers) : Measurable (euclideanAngularGlobal A J α hs ht E p) := by
  classical
  exact (euclideanAngularWeight_continuousOn A J α hs ht E p).measurable_piecewise continuousOn_const
    (angularDomain_closed A J α hs ht E p).measurableSet

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] [CompactSpace X] in
lemma euclideanDistanceGlobal_measurable (p : A.centers) : Measurable (euclideanDistanceGlobal A J α hs ht E p) := by
  classical
  exact ((angularChartCoordinates_continuousOn A J α hs ht E p).snd.sub
    (angularChartCoordinates_continuousOn A J α hs ht E p).fst).norm.measurable_piecewise continuousOn_const
    (angularDomain_closed A J α hs ht E p).measurableSet

include hE hD in
lemma separating_current_euclidean_angular_profile
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫ uv, euclideanAngularGlobal A J α hs ht E p uv *
        ((1+euclideanDistanceGlobal A J α hs ht E p uv/r)⁻¹)^6 ∂μ.prod μ) ≤ C*r^4 := by
  obtain ⟨F,hF,hgrowth⟩ := separating_current_euclidean_angular_moment A J α hs ht E hE D hD μ hann p
  let w := euclideanAngularGlobal A J α hs ht E p
  let d := euclideanDistanceGlobal A J α hs ht E p
  have hw := euclideanAngularGlobal_measurable A J α hs ht E p
  have hd := euclideanDistanceGlobal_measurable A J α hs ht E p
  have hw0 (uv) : 0 ≤ w uv := Set.indicator_nonneg (fun v _ => euclideanAngularWeight_nonneg A J α hs ht p v) uv
  have hd0 (uv) : 0 ≤ d uv := Set.indicator_nonneg (fun _ _ => norm_nonneg _) uv
  have hwi : Integrable w (μ.prod μ) := by
    refine (integrable_const (4:ℝ)).mono' hw.aestronglyMeasurable (ae_of_all _ fun uv => ?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (hw0 uv)]
    by_cases huv : uv ∈ angularDomain A J α hs ht E p
    · exact (Set.indicator_of_mem huv _).le.trans (euclideanAngularWeight_le A J α hs ht E p huv)
    · simp only [w,euclideanAngularGlobal,Set.indicator_of_notMem huv]; norm_num
  have he (s : ℝ) : {uv | d uv ≤ s}.indicator w = euclideanAngularNear A J α hs ht E s p := by
    funext uv
    by_cases huv : uv ∈ angularDomain A J α hs ht E p
    · simp [d,w,euclideanDistanceGlobal,euclideanAngularGlobal,euclideanAngularNear,euclideanNearSet,Set.indicator,huv]
    · simp [w,euclideanAngularGlobal,euclideanAngularNear,euclideanNearSet,Set.indicator,huv]
  refine ⟨32*F,by positivity,fun r hr => ?_⟩
  exact FourthShell.weighted_profile_bound (μ.prod μ) w d hw hd hw0 hd0 hwi F hF
    (fun s hs' => by rw [he]; exact hgrowth s hs') hr
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace TamingCompatibility.Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma profile_six_le_one {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    ((1+t/r)⁻¹)^6 ≤ 1 := by
  apply pow_le_one₀ (by positivity)
  apply inv_le_one_of_one_le₀
  have hh := div_nonneg ht hr.le
  linarith

lemma weighted_profile_integrable (w d : Ω → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ x, 0 ≤ w x) (hd0 : ∀ x, 0 ≤ d x) (hi : Integrable w μ)
    {r : ℝ} (hr : 0 < r) : Integrable (fun x => w x*((1+d x/r)⁻¹)^6) μ := by
  apply hi.mono' ((hw.mul ((measurable_const.add (hd.div_const r)).inv.pow_const 6)).aestronglyMeasurable)
  apply ae_of_all
  intro x
  change ‖w x*((1+d x/r)⁻¹)^6‖ ≤ w x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw0 x) (by positivity))]
  exact mul_le_of_le_one_right (hw0 x) (profile_six_le_one hr (hd0 x))

lemma weighted_radial_integrable (w d : Ω → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ x, 0 ≤ w x) (hd0 : ∀ x, 0 ≤ d x) (hi : Integrable w μ)
    {r : ℝ} (hr : 0 < r) : Integrable (fun x => w x*radialCoefficient r (d x)) μ := by
  have hm : Measurable (fun x => w x*radialCoefficient r (d x)) :=
    hw.mul (measurable_const.div ((measurable_const.add (hd.pow_const 2)).pow_const 4))
  apply ((weighted_profile_integrable w d hw hd hw0 hd0 hi hr).const_mul (8/r^4)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw0 x) (radialCoefficient_nonneg _ _))]
  calc
    _ ≤ w x*((8/r^4)*((1+d x/r)⁻¹)^6) := mul_le_mul_of_nonneg_left
      (radialCoefficient_profile hr (hd0 x)) (hw0 x)
    _ = _ := by ring

lemma weighted_radial_linear_integrable (w d : Ω → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ x, 0 ≤ w x) (hd0 : ∀ x, 0 ≤ d x) (hi : Integrable w μ)
    {r : ℝ} (hr : 0 < r) : Integrable (fun x => w x*radialCoefficient r (d x)*d x) μ := by
  have hm : Measurable (fun x => w x*radialCoefficient r (d x)*d x) :=
    (hw.mul (measurable_const.div ((measurable_const.add (hd.pow_const 2)).pow_const 4))).mul hd
  apply ((weighted_profile_integrable w d hw hd hw0 hd0 hi hr).const_mul (8/r^3)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (mul_nonneg (hw0 x) (radialCoefficient_nonneg _ _)) (hd0 x))]
  calc
    _ = w x*(radialCoefficient r (d x)*d x) := by ring
    _ ≤ w x*((8/r^3)*((1+d x/r)⁻¹)^6) := mul_le_mul_of_nonneg_left
      (radialCoefficient_linear_profile hr (hd0 x)) (hw0 x)
    _ = _ := by ring

lemma weighted_radial_estimates (w d : Ω → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ x, 0 ≤ w x) (hd0 : ∀ x, 0 ≤ d x) (hi : Integrable w μ)
    {C r : ℝ} (hr : 0 < r)
    (hbound : (∫ x, w x*((1+d x/r)⁻¹)^6 ∂μ) ≤ C*r^4) :
    (∫ x, w x*radialCoefficient r (d x) ∂μ) ≤ 8*C ∧
    (∫ x, w x*radialCoefficient r (d x)*d x ∂μ) ≤ 8*C*r := by
  have hp := weighted_profile_integrable w d hw hd hw0 hd0 hi hr
  constructor
  · calc
      _ ≤ ∫ x, (8/r^4)*(w x*((1+d x/r)⁻¹)^6) ∂μ := integral_mono
        (weighted_radial_integrable w d hw hd hw0 hd0 hi hr) (hp.const_mul _) (fun x => by
          have hh := mul_le_mul_of_nonneg_left (radialCoefficient_profile hr (hd0 x)) (hw0 x)
          nlinarith)
      _ = (8/r^4)*(∫ x, w x*((1+d x/r)⁻¹)^6 ∂μ) := integral_const_mul _ _
      _ ≤ (8/r^4)*(C*r^4) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 8*C := by field_simp
  · calc
      _ ≤ ∫ x, (8/r^3)*(w x*((1+d x/r)⁻¹)^6) ∂μ := integral_mono
        (weighted_radial_linear_integrable w d hw hd hw0 hd0 hi hr) (hp.const_mul _) (fun x => by
          have hh := mul_le_mul_of_nonneg_left (radialCoefficient_linear_profile hr (hd0 x)) (hw0 x)
          nlinarith)
      _ = (8/r^3)*(∫ x, w x*((1+d x/r)⁻¹)^6 ∂μ) := integral_const_mul _ _
      _ ≤ (8/r^3)*(C*r^4) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 8*C*r := by field_simp
end TamingCompatibility.Concentration

end
end

end OAI
