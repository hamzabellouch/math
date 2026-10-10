import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeInputInitial

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def kernelTestLinear (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (a : TwoForm X) (t : ℝ) (y : X) : FrameSpace A →L[ℝ] ℝ :=
  ∫ x, (framePairing A J α ht E a x).comp (K t x y) ∂geometricVolume A J α

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] in
lemma kernelTestLinear_measurable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : VolterraKernel.MeasurableKernel K) (a : TwoForm X) (ha : IsSmooth a) :
    StronglyMeasurable (Function.uncurry (kernelTestLinear A J α ht E K a)) := by
  let := geometricVolume_finite A J α hs ht
  have hφ := (framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable
  have hm : StronglyMeasurable (fun p : (ℝ × X) × X =>
      (framePairing A J α ht E a p.2).comp (K p.1.1 p.2 p.1.2)) :=
    (continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
      ((hφ.comp_measurable measurable_snd).prodMk
        (hK.comp_measurable (show Measurable (fun p : (ℝ × X) × X =>
          (p.1.1,p.2,p.1.2)) by fun_prop)))
  exact hm.integral_prod_right

include hE in
omit [SecondCountableTopology X] in
lemma kernelTestLinear_integrable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T) (y : X) :
    Integrable (fun x => (framePairing A J α ht E a x).comp (K t x y))
      (geometricVolume A J α) := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,_hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  have hi := hK.col_int t htp y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hi
  have hm : StronglyMeasurable (fun x => (framePairing A J α ht E a x).comp (K t x y)) :=
    (continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
    ((framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable.prodMk
      (hK.measurable.comp_measurable (measurable_const.prodMk (measurable_id.prodMk measurable_const))))
  apply (hi.const_mul B).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun x => (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hφ x) (norm_nonneg _))

include hE in
omit [SecondCountableTopology X] in
lemma kernelTestLinear_apply
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T) (y : X) (v : FrameSpace A) :
    kernelTestLinear A J α ht E K a t y v = kernelTestSlice A J α ht E K y v a t :=
  ContinuousLinearMap.integral_apply (kernelTestLinear_integrable A J α hs ht E hE K hK a ha htp y) v

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma kernelTestLinear_uniform_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc 0 T, ∀ y, ‖kernelTestLinear A J α ht E K a t y‖ ≤ B := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  refine ⟨B*H,mul_nonneg hB hK.nonneg,?_⟩
  intro t hp y
  have hi := hK.col_int t hp y
  have hb := hK.col t hp y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
  calc
    _ ≤ ∫ x, B*‖K t x y‖ ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (hi.const_mul B)
      exact Eventually.of_forall fun x => (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hφ x) (norm_nonneg _))
    _ = B*(∫ x, ‖K t x y‖ ∂geometricVolume A J α) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hB

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.MetricForms
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
lemma abs_pairing_le_sqrt {k : ℕ} (g : MetricModel.Metric V) (a b : Form V k) :
    |pairing g a b| ≤ Real.sqrt (pairing g a a) * Real.sqrt (pairing g b b) := by
  unfold pairing FormMetric.pairing
  simpa only [real_inner_self_eq_norm_sq,Real.sqrt_sq_eq_abs,abs_norm] using
    abs_real_inner_le_norm (FormMetric.sharp (a.compContinuousLinearMap (MetricModel.equiv g).toContinuousLinearMap))
      (FormMetric.sharp (b.compContinuousLinearMap (MetricModel.equiv g).toContinuousLinearMap))
end TamingCompatibility.MetricForms

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldLocalization ManifoldVolume MeasureTheory Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def pointNorm (a : TwoForm X) (x : X) : ℝ :=
  Real.sqrt (GeometricAdjoint.pairing J α ht a a x)

include hs in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma pointNorm_continuous (a : TwoForm X) (ha : IsSmooth a) :
    Continuous (pointNorm J α ht a) :=
  (GeometricAdjoint.pairing_two_smooth J α hs ht ha ha).continuous.sqrt

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma pointNorm_sq (a : TwoForm X) (x : X) :
    pointNorm J α ht a x ^ 2 = GeometricAdjoint.pairing J α ht a a x :=
  Real.sq_sqrt (MetricForms.pairing_self_nonneg _ _)

lemma pointNorm_integral_sq (a : PreL2 A J α hs ht true) :
    (∫ x, pointNorm J α ht a.val x ^ 2 ∂geometricVolume A J α) = ‖a‖^2 := by
  simp_rw [pointNorm_sq]
  exact (preL2_norm_sq A J α hs ht true a).symm

lemma pointNorm_product_integral (a b : PreL2 A J α hs ht true) :
    (∫ x, pointNorm J α ht a.val x * pointNorm J α ht b.val x ∂geometricVolume A J α) ≤ ‖a‖*‖b‖ := by
  let := geometricVolume_finite A J α hs ht
  have ha := (pointNorm_continuous J α hs ht a.val a.property).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := geometricVolume A J α) (p := ENNReal.ofReal 2)
  have hb := (pointNorm_continuous J α hs ht b.val b.property).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := geometricVolume A J α) (p := ENNReal.ofReal 2)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := geometricVolume A J α)
    (f := pointNorm J α ht a.val) (g := pointNorm J α ht b.val)
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (Eventually.of_forall (fun x => Real.sqrt_nonneg _))
    (Eventually.of_forall (fun x => Real.sqrt_nonneg _)) ha hb
  simpa only [Real.rpow_two,show (1:ℝ)/2 = 1/2 from rfl,← Real.sqrt_eq_rpow,
    pointNorm_integral_sq,Real.sqrt_sq_eq_abs,abs_norm] using hh

lemma bounded_pairing_integrable (a b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    Integrable (fun x => f x * GeometricAdjoint.pairing J α ht a.val b.val x) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  have hi := (((pointNorm_continuous J α hs ht a.val a.property).mul
    (pointNorm_continuous J α hs ht b.val b.property)).integrable_of_hasCompactSupport
      (μ := geometricVolume A J α) (HasCompactSupport.of_compactSpace _)).const_mul C
  apply hi.mono' (hfm.mul (GeometricAdjoint.pairing_two_smooth J α hs ht a.property b.property).continuous.aestronglyMeasurable)
  filter_upwards [hf] with x hx
  dsimp only [Pi.mul_apply]
  erw [norm_mul,Real.norm_eq_abs]
  exact mul_le_mul hx (MetricForms.abs_pairing_le_sqrt _ _ _) (abs_nonneg _) hC

lemma bounded_pairing_integral_bound (a b : PreL2 A J α hs ht true)
    (f : X → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    ‖∫ x, f x * GeometricAdjoint.pairing J α ht a.val b.val x ∂geometricVolume A J α‖ ≤ C*‖a‖*‖b‖ := by
  let := geometricVolume_finite A J α hs ht
  have hi := (((pointNorm_continuous J α hs ht a.val a.property).mul
    (pointNorm_continuous J α hs ht b.val b.property)).integrable_of_hasCompactSupport
      (μ := geometricVolume A J α) (HasCompactSupport.of_compactSpace _)).const_mul C
  calc
    _ ≤ ∫ x, C*(pointNorm J α ht a.val x * pointNorm J α ht b.val x) ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [hf] with x hx
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul hx (MetricForms.abs_pairing_le_sqrt _ _ _) (abs_nonneg _) hC
    _ = C*(∫ x, pointNorm J α ht a.val x * pointNorm J α ht b.val x ∂geometricVolume A J α) := integral_const_mul _ _
    _ ≤ C*(‖a‖*‖b‖) := mul_le_mul_of_nonneg_left (pointNorm_product_integral A J α hs ht a b) hC
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
