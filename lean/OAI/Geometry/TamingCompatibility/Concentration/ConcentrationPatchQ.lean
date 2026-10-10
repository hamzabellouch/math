import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationPatchError

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma physicalGradientMass_mul_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {V : Type*} [NormedAddCommGroup V] (q : X → V)
    (hq : Integrable q (geometricVolume A J α)) {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    Integrable (fun x => ‖q x‖*physicalGradientMass J α hs ht μ L r x) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  apply (physicalQError_product_integrable A J α hs ht μ q hq hL hr).integral_prod_right.congr
  apply Eventually.of_forall
  intro x
  simp_rw [physicalProfile_symm J α hs ht (L*r) _ x]
  rw [integral_div,integral_const_mul]
  simp only [physicalGradientMass,physicalProfileMass,mul_div_assoc]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma physicalGradientMass_nonneg
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (L : ℝ) {r : ℝ} (hr : 0 < r) (x : X) :
    0 ≤ physicalGradientMass J α hs ht μ L r x :=
  div_nonneg (physicalProfileMass_nonneg J α hs ht μ _ _) (by positivity)

include hE in
lemma concentrationPatch_Q_control
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true) (p : A.centers) :
    ∃ e : ℝ → X → ℝ,
      (∀ r, 0 < r → ∀ x, 0 ≤ e r x) ∧
      (∀ r, 0 < r → Integrable (e r) (geometricVolume A J α)) ∧
      Tendsto (fun r => ∫ x, e r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x,
        ‖l2Coefficients A J α hs ht E hE Q x‖ *
          ‖normalizedFrameEncode A J α ht E x
            (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val x)‖ ≤ C*e r x := by
  let := geometricVolume_finite A J α hs ht
  let q := l2Coefficients A J α hs ht E hE Q
  have hq : Integrable q (geometricVolume A J α) := (Lp.memLp q).integrable (by norm_num)
  obtain ⟨B,C,L,hB,hC,hL,hgrad⟩ := localConcentration_gradient_bound A J α hs ht E hE μ p
  obtain ⟨D,L',hD,hL',hlocal⟩ := localConcentration_physical_bound A J α hs ht E hE μ p
  let e := fun r x => D*(‖q x‖*physicalGradientMass J α hs ht μ L' r x)+
    B*(‖q x‖*physicalGradientMass J α hs ht μ L r x)+C*r^4*‖q x‖
  have he (r) (hr : 0 < r) (x) : 0 ≤ e r x := by
    exact add_nonneg (add_nonneg
      (mul_nonneg hD (mul_nonneg (norm_nonneg _) (physicalGradientMass_nonneg J α hs ht μ L' hr x)))
      (mul_nonneg hB (mul_nonneg (norm_nonneg _) (physicalGradientMass_nonneg J α hs ht μ L hr x))))
      (mul_nonneg (by positivity) (norm_nonneg _))
  have hi (r) (hr : 0 < r) : Integrable (e r) (geometricVolume A J α) :=
    (((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL' hr).const_mul D).add
      ((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL hr).const_mul B)).add
      (hq.norm.const_mul (C*r^4))
  have heq (r) (hr : 0 < r) : (∫ x, e r x ∂geometricVolume A J α) =
      D*(∫ x, ‖q x‖*physicalGradientMass J α hs ht μ L' r x ∂geometricVolume A J α)+
      B*(∫ x, ‖q x‖*physicalGradientMass J α hs ht μ L r x ∂geometricVolume A J α)+
      (C*r^4)*(∫ x, ‖q x‖ ∂geometricVolume A J α) := by
    dsimp only [e]
    erw [integral_add (((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL' hr).const_mul D).add
      ((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL hr).const_mul B)) (hq.norm.const_mul (C*r^4)),
      integral_add ((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL' hr).const_mul D)
        ((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL hr).const_mul B),
      integral_const_mul,integral_const_mul,integral_const_mul]
  have he0 : Tendsto (fun r => ∫ x, e r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 := physicalGradientMass_L2_limit A J α hs ht μ hann q (Lp.memLp q) hL'
    have h2 := physicalGradientMass_L2_limit A J α hs ht μ hann q (Lp.memLp q) hL
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    have hh := ((h1.const_mul D).add (h2.const_mul B)).add (((hr.pow 4).const_mul C).mul_const (∫ x, ‖q x‖ ∂geometricVolume A J α))
    simp only [zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul,add_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (heq r hr).symm
  refine ⟨e,he,hi,he0,fun θ => ?_⟩
  obtain ⟨K,hK,hcoef⟩ := concentrationPatch_coefficient_bound A J α hs ht E hE p θ
  refine ⟨K,hK,fun r hr hr1 x => ?_⟩
  by_cases hx : x ∈ tsupport (A.partition p)
  · have hg := hgrad x hx r hr
    have hl := hlocal x hx r hr
    have hχ := A.partition.nonneg p x
    have hχ1 := A.partition.le_one p x
    have hp : (D/r^2)*physicalProfileMass J α hs ht μ (L'*r) x ≤
        D*physicalGradientMass J α hs ht μ L' r x := by
      calc
        _ = D*r*physicalGradientMass J α hs ht μ L' r x := by dsimp only [physicalGradientMass]; field_simp
        _ = (D*physicalGradientMass J α hs ht μ L' r x)*r := by ring
        _ ≤ (D*physicalGradientMass J α hs ht μ L' r x)*1 := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hD (physicalGradientMass_nonneg J α hs ht μ L' hr x))
        _ = _ := mul_one _
    have hb : localConcentration A J α hs ht E μ p r (extChartAt Model p.val x)+
        A.partition p x*‖fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x)‖ ≤
      D*physicalGradientMass J α hs ht μ L' r x+B*physicalGradientMass J α hs ht μ L r x+C*r^4 := by
      have hmul := mul_le_of_le_one_left (norm_nonneg (fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x))) hχ1
      linarith
    have hh := mul_le_mul_of_nonneg_left ((hcoef μ r hr x hx).trans (mul_le_mul_of_nonneg_left hb hK)) (norm_nonneg (q x))
    exact hh.trans_eq (by dsimp only [e,q]; ring)
  · rw [concentrationPatch_wedge_zero_off A J α hs ht E μ p r θ.val hx]
    erw [map_zero,norm_zero,mul_zero]
    exact mul_nonneg hK (he r hr x)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
