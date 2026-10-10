import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLeadingDuhamel

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

include hE in
lemma kernelInputTest_time_integrable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htT : t ≤ T)
    (v : X → FrameSpace A) (hm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) :
    IntegrableOn (fun s => kernelInputTest A J α ht E K a s v) (Ioo 0 t) := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,_hB,hb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE K hK a ha hV
  apply Integrable.of_bound (kernelInputTest_time_measurable A J α hs ht E hE K hK.measurable a ha v hm).aestronglyMeasurable B
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hp
  exact hb s ⟨hp.1,hp.2.le.trans htT⟩ v hv

include hE in
omit [SecondCountableTopology X] in
lemma kernelInputTest_sum_zero
    (K L M : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H B C T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T B L)
    (hM : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C M)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (heq : ∀ x y, K t x y + L t x y + M t x y = 0)
    (v : X → FrameSpace A) (hm : StronglyMeasurable v) {V : ℝ} (hv : ∀ y, ‖v y‖ ≤ V) :
    kernelInputTest A J α ht E K a t v + kernelInputTest A J α ht E L a t v +
      kernelInputTest A J α ht E M a t v = 0 := by
  have hiK := kernelTestLinear_input_integrable A J α hs ht E hE K hK a ha htp v hm hv
  have hiL := kernelTestLinear_input_integrable A J α hs ht E hE L hL a ha htp v hm hv
  have hiM := kernelTestLinear_input_integrable A J α hs ht E hE M hM a ha htp v hm hv
  unfold kernelInputTest
  have hiKL : Integrable (fun y => kernelTestLinear A J α ht E K a t y (v y) +
      kernelTestLinear A J α ht E L a t y (v y)) (geometricVolume A J α) := hiK.add hiL
  rw [← integral_add hiK hiL,← integral_add hiKL hiM]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  have hK' := kernelTestLinear_integrable A J α hs ht E hE K hK a ha htp y
  have hL' := kernelTestLinear_integrable A J α hs ht E hE L hL a ha htp y
  have hM' := kernelTestLinear_integrable A J α hs ht E hE M hM a ha htp y
  have iK := hK'.apply_continuousLinearMap (v y)
  have iL := hL'.apply_continuousLinearMap (v y)
  have iM := hM'.apply_continuousLinearMap (v y)
  rw [kernelTestLinear_apply A J α hs ht E hE K hK a ha htp y (v y),
    kernelTestLinear_apply A J α hs ht E hE L hL a ha htp y (v y),
    kernelTestLinear_apply A J α hs ht E hE M hM a ha htp y (v y)]
  change (∫ x, framePairing A J α ht E a x (K t x y (v y)) ∂geometricVolume A J α) +
    (∫ x, framePairing A J α ht E a x (L t x y (v y)) ∂geometricVolume A J α) +
    (∫ x, framePairing A J α ht E a x (M t x y (v y)) ∂geometricVolume A J α) = 0
  change Integrable (fun x => framePairing A J α ht E a x (K t x y (v y))) _ at iK
  change Integrable (fun x => framePairing A J α ht E a x (L t x y (v y))) _ at iL
  change Integrable (fun x => framePairing A J α ht E a x (M t x y (v y))) _ at iM
  have iKL : Integrable (fun x => framePairing A J α ht E a x (K t x y (v y)) +
      framePairing A J α ht E a x (L t x y (v y))) (geometricVolume A J α) := iK.add iL
  rw [← integral_add iK iL,← integral_add iKL iM]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  rw [← map_add,← map_add]
  have hh := congrArg (fun F : FrameSpace A →L[ℝ] FrameSpace A => F (v y)) (heq x y)
  change K t x y (v y) + L t x y (v y) + M t x y (v y) = 0 at hh
  rw [hh,map_zero]
  rfl

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
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma candidate_primitive_of_cancellation
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {C T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C K)
    (heq : ∀ s ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A E s x y + K s x y +
      VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E) K s x y = 0)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (a : PreL2 A J α hs ht true)
    {t : ℝ} (htp : t ∈ Ioc 0 T) :
    kernelInputTest A J α ht E (globalLeading J α ht A E) a.val t v +
      kernelInputTest A J α ht E
        (VolterraKernel.convolution (geometricVolume A J α) (globalLeading J α ht A E) K) a.val t v =
      (∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) -
        ∫ s in Ioo 0 t,
          kernelInputTest A J α ht E (globalLeading J α ht A E)
            (hodgeLaplacian A J α hs ht a).val s v +
          kernelInputTest A J α ht E
            (VolterraKernel.convolution (geometricVolume A J α) (globalLeading J α ht A E) K)
            (hodgeLaplacian A J α hs ht a).val s v := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  have hRt := hR.mono_time (geometricVolume A J α) hT1
  have hLt := hL.mono_time (geometricVolume A J α) hT1
  have hRK := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ K hRt hK
  have hPK := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ K hLt hK
  have hRa := kernelInputTest_time_integrable A J α hs ht E hE _ hRt a.val a.property htp.2 v hvm hV hv
  have hKa := kernelInputTest_time_integrable A J α hs ht E hE K hK a.val a.property htp.2 v hvm hV hv
  have hRKa := kernelInputTest_time_integrable A J α hs ht E hE _ hRK a.val a.property htp.2 v hvm hV hv
  have hPD := kernelInputTest_time_integrable A J α hs ht E hE _ hLt
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property htp.2 v hvm hV hv
  have hPKD := kernelInputTest_time_integrable A J α hs ht E hE _ hPK
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property htp.2 v hvm hV hv
  have hpa := kernelInputTest_leading_primitive A J α hs ht E hE v hvm hV hv a htp.1 (htp.2.trans hT1)
  have hea := leading_convolution_primitive A J α hs ht E hE K hK v hvm hV hv a htp (htp.2.trans hT1)
  rw [integral_sub hRa hPD] at hpa
  rw [integral_sub hRKa hPKD] at hea
  have hsum : IntegrableOn (fun s =>
      kernelInputTest A J α ht E (globalResidual J α ht A E) a.val s v +
      kernelInputTest A J α ht E K a.val s v) (Ioo 0 t) := hRa.add hKa
  have hz : (∫ s in Ioo 0 t,
      kernelInputTest A J α ht E (globalResidual J α ht A E) a.val s v +
      kernelInputTest A J α ht E K a.val s v +
      kernelInputTest A J α ht E
        (VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E) K) a.val s v) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hp
    have hp' : s ∈ Ioc 0 T := ⟨hp.1,hp.2.le.trans htp.2⟩
    exact kernelInputTest_sum_zero A J α hs ht E hE _ K _ hRt hK hRK a.val a.property hp'
      (heq s hp') v hvm hv
  rw [integral_add hsum hRKa,integral_add hRa hKa] at hz
  rw [integral_add hPD hPKD]
  linarith

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
