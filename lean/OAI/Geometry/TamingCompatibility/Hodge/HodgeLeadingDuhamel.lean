import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeBoundedInputPrimitive
import OAI.Geometry.TamingCompatibility.Hodge.HodgeInputDuhamel

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
lemma leading_test_duhamel
    (W : ℝ → X → FrameSpace A) (hW : StronglyMeasurable (Function.uncurry W))
    {V t : ℝ} (hV : 0 ≤ V) (_htp : 0 < t) (ht1 : t ≤ 1)
    (hWb : ∀ s ∈ Ioo 0 t, ∀ y, ‖W s y‖ ≤ V)
    (a : PreL2 A J α hs ht true) :
    (∫ s in Ioo 0 t, kernelInputTest A J α ht E (globalLeading J α ht A E) a.val (t-s) (W s)) =
      (∫ s in Ioo 0 t, ∫ y, framePairing A J α ht E a.val y (W s y) ∂geometricVolume A J α) +
        ∫ u in Ioo 0 t, ∫ s in Ioo 0 u,
          kernelInputTest A J α ht E (globalResidual J α ht A E) a.val (u-s) (W s) -
          kernelInputTest A J α ht E (globalLeading J α ht A E)
            (hodgeLaplacian A J α hs ht a).val (u-s) (W s) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  obtain ⟨BR,hBR,hRb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hR a.val a.property hV
  obtain ⟨BP,hBP,hPb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hL a.val a.property hV
  obtain ⟨BD,hBD,hDb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hL
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property hV
  have hPm := kernelInputTest_shift_measurable A J α hs ht E hE _ hL.measurable a.val a.property W hW
  have hRm := kernelInputTest_shift_measurable A J α hs ht E hE _ hR.measurable a.val a.property W hW
  have hDm := kernelInputTest_shift_measurable A J α hs ht E hE _ hL.measurable
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property W hW
  have hAm : StronglyMeasurable (fun s => ∫ y, framePairing A J α ht E a.val y (W s y) ∂geometricVolume A J α) := by
    have hm : StronglyMeasurable (fun p : ℝ × X => framePairing A J α ht E a.val p.2 (W p.1 p.2)) :=
      (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
        (((framePairing_continuous A J α hs ht E hE a.val a.property).stronglyMeasurable.comp_measurable measurable_snd).prodMk hW)
    exact hm.integral_prod_right
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a.val a.property
  apply TimeTriangle.integrated_primitive
  · apply Integrable.of_bound
      (hPm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable BP
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsp
    exact hPb (t-s) ⟨sub_pos.mpr hsp.2,(sub_le_self _ hsp.1.le).trans ht1⟩ (W s) (hWb s hsp)
  · apply Integrable.of_bound hAm.aestronglyMeasurable ((geometricVolume A J α).real univ*(B*V))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsp
    calc
      _ ≤ ∫ y : X, B*V ∂geometricVolume A J α := by
        apply norm_integral_le_of_norm_le (integrable_const _)
        exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hφ y) (hWb s hsp y) (norm_nonneg _) hB)
      _ = _ := by simp [integral_const,smul_eq_mul]
  · exact hRm.sub hDm
  · exact add_nonneg hBR hBD
  · intro s hsp u hup
    have hp : u-s ∈ Ioc 0 1 := ⟨sub_pos.mpr hup.1,by linarith [hup.2,hsp.1]⟩
    exact (norm_sub_le _ _).trans (add_le_add (hRb _ hp (W s) (hWb s hsp))
      (hDb _ hp (W s) (hWb s hsp)))
  · intro s hsp
    rw [TimeTriangle.integral_shift (fun q =>
      kernelInputTest A J α ht E (globalResidual J α ht A E) a.val q (W s) -
      kernelInputTest A J α ht E (globalLeading J α ht A E)
        (hodgeLaplacian A J α hs ht a).val q (W s)) hsp.2.le]
    exact (kernelInputTest_leading_primitive A J α hs ht E hE (W s)
      (hW.comp_measurable (measurable_const.prodMk measurable_id)) hV (hWb s hsp) a
      (sub_pos.mpr hsp.2) (by linarith [hsp.1])).symm

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
lemma leading_convolution_primitive
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {C T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C K)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (a : PreL2 A J α hs ht true)
    {t : ℝ} (htp : t ∈ Ioc 0 T) (ht1 : t ≤ 1) :
    kernelInputTest A J α ht E
        (VolterraKernel.convolution (geometricVolume A J α) (globalLeading J α ht A E) K) a.val t v =
      (∫ s in Ioo 0 t, kernelInputTest A J α ht E K a.val s v) +
        ∫ u in Ioo 0 t,
          kernelInputTest A J α ht E
            (VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E) K) a.val u v -
          kernelInputTest A J α ht E
            (VolterraKernel.convolution (geometricVolume A J α) (globalLeading J α ht A E) K)
            (hodgeLaplacian A J α hs ht a).val u v := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  let W := fun s => KernelL2.action (geometricVolume A J α) (K s) v
  have hW := KernelL2.time_action_measurable (geometricVolume A J α) K hK.measurable v hvm
  have hWb (s : ℝ) (hsp : s ∈ Ioc 0 T) (y : X) : ‖W s y‖ ≤ C*V := by
    have hi := hK.row_int s hsp y
    have hb := hK.row s hsp y
    simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
    exact KernelL2.action_norm (geometricVolume A J α) (K s) v hV hv y hi hb
  have hCV := mul_nonneg hK.nonneg hV
  have hkt := hK.mono_time (geometricVolume A J α) htp.2
  have hlt := hL.mono_time (geometricVolume A J α) ht1
  have hrt := hR.mono_time (geometricVolume A J α) ht1
  have hh := leading_test_duhamel A J α hs ht E hE W hW hCV htp.1 ht1
    (fun s hp => hWb s ⟨hp.1,hp.2.le.trans htp.2⟩) a
  rw [kernelInputTest_convolution A J α hs ht E hE _ K hlt hkt a.val a.property
    ⟨htp.1,le_rfl⟩ v hvm hV hv]
  refine hh.trans ?_
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro s hp
    exact (kernelInputTest_action A J α hs ht E hE K hK a.val a.property
      ⟨hp.1,hp.2.le.trans htp.2⟩ v hvm hv).symm
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro u hup
    obtain ⟨BR,_hBR,hRb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hR a.val a.property hCV
    obtain ⟨BD,_hBD,hDb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hL
      (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property hCV
    have hiR : IntegrableOn (fun s => kernelInputTest A J α ht E (globalResidual J α ht A E) a.val (u-s) (W s)) (Ioo 0 u) := by
      apply Integrable.of_bound ((kernelInputTest_shift_measurable A J α hs ht E hE _ hR.measurable a.val a.property W hW).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable BR
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hp
      exact hRb (u-s) ⟨sub_pos.mpr hp.2,by linarith [hup.2,hp.1]⟩ (W s)
        (hWb s ⟨hp.1,hp.2.le.trans (hup.2.le.trans htp.2)⟩)
    have hiD : IntegrableOn (fun s => kernelInputTest A J α ht E (globalLeading J α ht A E)
        (hodgeLaplacian A J α hs ht a).val (u-s) (W s)) (Ioo 0 u) := by
      apply Integrable.of_bound ((kernelInputTest_shift_measurable A J α hs ht E hE _ hL.measurable
        (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property W hW).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable BD
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hp
      exact hDb (u-s) ⟨sub_pos.mpr hp.2,by linarith [hup.2,hp.1]⟩ (W s)
        (hWb s ⟨hp.1,hp.2.le.trans (hup.2.le.trans htp.2)⟩)
    dsimp only
    rw [integral_sub hiR hiD]
    rw [kernelInputTest_convolution A J α hs ht E hE _ K hrt hkt a.val a.property
      ⟨hup.1,hup.2.le⟩ v hvm hV hv,
      kernelInputTest_convolution A J α hs ht E hE _ K hlt hkt
        (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property
        ⟨hup.1,hup.2.le⟩ v hvm hV hv]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
