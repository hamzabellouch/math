import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeVolterraPairing

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

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma bounded_input_leading_primitive (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    {V : ℝ} (_hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in Ioo 0 t, ∫ y,
      (kernelTestLinear A J α ht E (globalResidual J α ht A E) a.val s y -
       kernelTestLinear A J α ht E (globalLeading J α ht A E)
         (hodgeLaplacian A J α hs ht a).val s y) (v y) ∂geometricVolume A J α) =
      ∫ y, kernelTestLinear A J α ht E (globalLeading J α ht A E) a.val t y (v y) -
        framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  obtain ⟨B,hB,hRb⟩ := kernelTestLinear_uniform_bound A J α hs ht E hE _ hR a.val a.property
  obtain ⟨C,hC,hLb⟩ := kernelTestLinear_uniform_bound A J α hs ht E hE _ hL
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property
  let G := fun p : ℝ × X =>
    (kernelTestLinear A J α ht E (globalResidual J α ht A E) a.val p.1 p.2 -
     kernelTestLinear A J α ht E (globalLeading J α ht A E)
       (hodgeLaplacian A J α hs ht a).val p.1 p.2) (v p.2)
  have hm : StronglyMeasurable G := by
    exact (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (((kernelTestLinear_measurable A J α hs ht E hE _ hR.measurable a.val a.property).sub
      (kernelTestLinear_measurable A J α hs ht E hE _ hL.measurable
        (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property)).prodMk
      (hvm.comp_measurable measurable_snd))
  have hi : Integrable G ((volume.restrict (Ioo 0 t)).prod (geometricVolume A J α)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable ((B+C)*V)
    have hp : ∀ᵐ p : ℝ × X ∂(volume.restrict (Ioo 0 t)).prod (geometricVolume A J α),
        p.1 ∈ Ioo 0 t := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs'
      exact Eventually.of_forall fun _ => hs'
    filter_upwards [hp] with p hp
    have hpt : p.1 ∈ Ioc 0 1 := ⟨hp.1,hp.2.le.trans ht1⟩
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul ((norm_sub_le _ _).trans (add_le_add (hRb _ hpt _) (hLb _ hpt _)))
        (hv _) (norm_nonneg _) (add_nonneg hB hC))
  calc
    _ = ∫ y, (∫ s in Ioo 0 t, G (s,y)) ∂geometricVolume A J α := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [kernelTestLinear_apply A J α hs ht E hE _ hL a.val a.property ⟨htp,ht1⟩ y (v y)]
      rw [← leading_time_primitive A J α hs ht E hE y (v y) a htp ht1,
        intervalIntegral.integral_of_le htp.le, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hp
      have hsp : s ∈ Ioc 0 1 := ⟨hp.1,hp.2.le.trans ht1⟩
      change kernelTestLinear A J α ht E (globalResidual J α ht A E) a.val s y (v y) -
        kernelTestLinear A J α ht E (globalLeading J α ht A E)
          (hodgeLaplacian A J α hs ht a).val s y (v y) = _
      rw [kernelTestLinear_apply A J α hs ht E hE _ hR a.val a.property hsp y (v y),
        kernelTestLinear_apply A J α hs ht E hE _ hL
          (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property hsp y (v y)]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

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

include hE in
omit [SecondCountableTopology X] in
lemma kernelTestLinear_input_integrable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (v : X → FrameSpace A) (hm : StronglyMeasurable v) {V : ℝ} (hv : ∀ y, ‖v y‖ ≤ V) :
    Integrable (fun y => kernelTestLinear A J α ht E K a t y (v y)) (geometricVolume A J α) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := kernelTestLinear_uniform_bound A J α hs ht E hE K hK a ha
  have hkm : StronglyMeasurable (fun y => kernelTestLinear A J α ht E K a t y) := (kernelTestLinear_measurable A J α hs ht E hE K hK.measurable a ha).comp_measurable
    (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
    (hkm.prodMk hm)).aestronglyMeasurable (B*V)
  exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (hφ t htp y) (hv y) (norm_nonneg _) hB)

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma kernelInputTest_uniform_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {V : ℝ} (hV : 0 ≤ V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc 0 T, ∀ v : X → FrameSpace A,
      (∀ y, ‖v y‖ ≤ V) → ‖kernelInputTest A J α ht E K a t v‖ ≤ B := by
  obtain ⟨B,hB,hφ⟩ := kernelTestLinear_uniform_bound A J α hs ht E hE K hK a ha
  refine ⟨(geometricVolume A J α).real univ*(B*V),by positivity,?_⟩
  intro t hp v hv
  exact kernelInputTest_bound A J α hs ht E K a t v hB (hφ t hp) hv

include hs hE in
omit [ConnectedSpace X] in
lemma kernelInputTest_time_measurable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : VolterraKernel.MeasurableKernel K) (a : TwoForm X) (ha : IsSmooth a)
    (v : X → FrameSpace A) (hm : StronglyMeasurable v) :
    StronglyMeasurable (fun t => kernelInputTest A J α ht E K a t v) := by
  have hh := kernelInputTest_shift_measurable A J α hs ht E hE K hK a ha
    (fun _ => v) (hm.comp_measurable measurable_snd)
  simpa [Function.comp_def] using hh.comp_measurable (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian
include hE in
lemma kernelInputTest_leading_primitive
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in Ioo 0 t,
      kernelInputTest A J α ht E (globalResidual J α ht A E) a.val s v -
      kernelInputTest A J α ht E (globalLeading J α ht A E)
        (hodgeLaplacian A J α hs ht a).val s v) =
      kernelInputTest A J α ht E (globalLeading J α ht A E) a.val t v -
        ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a.val a.property
  have hiφ : Integrable (fun y => framePairing A J α ht E a.val y (v y)) (geometricVolume A J α) := by
    apply Integrable.of_bound ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((framePairing_continuous A J α hs ht E hE a.val a.property).stronglyMeasurable.prodMk hvm)).aestronglyMeasurable (B*V)
    exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hφ y) (hv y) (norm_nonneg _) hB)
  have hp := bounded_input_leading_primitive A J α hs ht E hE v hvm hV hv a htp ht1
  rw [integral_sub (kernelTestLinear_input_integrable A J α hs ht E hE _ hL a.val a.property
    ⟨htp,ht1⟩ v hvm hv) hiφ] at hp
  refine Eq.trans ?_ hp
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hsp
  have hst : s ∈ Ioc 0 1 := ⟨hsp.1,hsp.2.le.trans ht1⟩
  exact (integral_sub
    (kernelTestLinear_input_integrable A J α hs ht E hE _ hR a.val a.property hst v hvm hv)
    (kernelTestLinear_input_integrable A J α hs ht E hE _ hL
      (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property hst v hvm hv)).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
