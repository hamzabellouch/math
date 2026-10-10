import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalCorrection

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelL2
open MeasureTheory Set Filter
variable {X F : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]
  [SecondCountableTopology X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (K L : ℝ → X → X → F →L[ℝ] F) {T A C : ℝ}
  (hK : VolterraKernel.HeatBound μ 0 T A K) (hL : VolterraKernel.HeatBound μ 0 T C L)

omit [BorelSpace X] [CompleteSpace F] in
lemma time_action_measurable (hKm : VolterraKernel.MeasurableKernel K)
    (v : X → F) (hvm : StronglyMeasurable v) :
    StronglyMeasurable (fun p : ℝ × X => action μ (K p.1) v p.2) := by
  have hm : StronglyMeasurable (fun p : (ℝ × X) × X => K p.1.1 p.1.2 p.2 (v p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hKm.comp_measurable (show Measurable (fun p : (ℝ × X) × X => (p.1.1,p.1.2,p.2)) by fun_prop)).prodMk (hvm.comp_measurable measurable_snd))
  exact hm.integral_prod_right

include hK hL in
omit [BorelSpace X] [CompleteSpace F] in
lemma shifted_action_measurable (t : ℝ) (v : X → F) (hvm : StronglyMeasurable v) :
    StronglyMeasurable (fun p : ℝ × X => action μ (K (t-p.1)) (action μ (L p.1) v) p.2) := by
  have hLm := time_action_measurable μ L hL.measurable v hvm
  have hm : StronglyMeasurable (fun p : (ℝ × X) × X => K (t-p.1.1) p.1.2 p.2
      (action μ (L p.1.1) v p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hK.measurable.comp_measurable (show Measurable (fun p : (ℝ × X) × X => (t-p.1.1,p.1.2,p.2)) by fun_prop)).prodMk
        (hLm.comp_measurable (measurable_fst.fst.prodMk measurable_snd)))
  exact hm.integral_prod_right

include hK hL in
lemma convolution_pairing {t : ℝ} (ht : t ∈ Ioc 0 T)
    (v : X → F) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (φ : X → F →L[ℝ] ℝ) (hφm : StronglyMeasurable φ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ x, ‖φ x‖ ≤ B) :
    (∫ x, φ x (action μ (VolterraKernel.convolution μ K L t) v x) ∂μ) =
      ∫ s in Ioo 0 t, ∫ x, φ x (action μ (K (t-s)) (action μ (L s) v) x) ∂μ := by
  have hm := shifted_action_measurable μ K L hK hL t v hvm
  have hn (s : ℝ) (hs : s ∈ Ioo 0 t) (x : X) :
      ‖action μ (K (t-s)) (action μ (L s) v) x‖ ≤ A*(C*V) := by
    have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2,(sub_le_self _ hs.1.le).trans ht.2⟩
    have hb : s ∈ Ioc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
    have hKi := hK.row_int (t-s) ha x
    have hKb := hK.row (t-s) ha x
    have hLi (z : X) := hL.row_int s hb z
    have hLb (z : X) := hL.row s hb z
    simp only [VolterraBounds.weight,pow_zero,one_mul] at hKi hKb hLi hLb
    exact action_norm μ (K (t-s)) (action μ (L s) v) (mul_nonneg hL.nonneg hV)
      (fun z => action_norm μ (L s) v hV hv z (hLi z) (hLb z)) x hKi hKb
  have htm : StronglyMeasurable (fun p : ℝ × X =>
      φ p.2 (action μ (K (t-p.1)) (action μ (L p.1) v) p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hφm.comp_measurable measurable_snd).prodMk hm)
  have hi : Integrable (fun p : ℝ × X =>
      φ p.2 (action μ (K (t-p.1)) (action μ (L p.1) v) p.2))
      ((volume.restrict (Ioo 0 t)).prod μ) := by
    apply Integrable.of_bound htm.aestronglyMeasurable (B*(A*(C*V)))
    have hp : ∀ᵐ p : ℝ × X ∂(volume.restrict (Ioo 0 t)).prod μ, p.1 ∈ Ioo 0 t := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact Eventually.of_forall fun _ => hs
    filter_upwards [hp] with p hp
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hφ p.2) (hn p.1 hp p.2) (norm_nonneg _) hB)
  calc
    _ = ∫ x, φ x (∫ s in Ioo 0 t, action μ (K (t-s)) (action μ (L s) v) x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [convolution_action μ K L hK hL ht v hvm hV hv x]
    _ = ∫ x, (∫ s in Ioo 0 t, φ x (action μ (K (t-s)) (action μ (L s) v) x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply ((φ x).integral_comp_comm _).symm
      apply Integrable.of_bound
        ((hm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
        (A*(C*V))
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hn s hs x
    _ = _ := (integral_integral_swap hi).symm

end TamingCompatibility.GeometricHilbert.KernelL2

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

def kernelInputTest (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (a : TwoForm X) (t : ℝ) (v : X → FrameSpace A) : ℝ :=
  ∫ y, kernelTestLinear A J α ht E K a t y (v y) ∂geometricVolume A J α

include hE in
omit [SecondCountableTopology X] in
lemma kernelInputTest_eq_weakAction
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (v : X → FrameSpace A) :
    kernelInputTest A J α ht E K a t v = kernelWeakAction A J α ht E K v a t := by
  apply integral_congr_ae
  filter_upwards [] with y
  exact kernelTestLinear_apply A J α hs ht E hE K hK a ha htp y (v y)

include hE in
omit [SecondCountableTopology X] in
lemma kernelInputTest_action
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v) {V : ℝ} (hv : ∀ y, ‖v y‖ ≤ V) :
    kernelInputTest A J α ht E K a t v =
      ∫ x, framePairing A J α ht E a x (KernelL2.action (geometricVolume A J α) (K t) v x)
        ∂geometricVolume A J α := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  have hsup := hK.sup t htp
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hsup
  rw [kernelInputTest_eq_weakAction A J α hs ht E hE K hK a ha htp v]
  exact (KernelL2.action_test_swap (geometricVolume A J α) (K t)
    (VolterraKernel.kernel_section K hK.measurable t) v hvm (framePairing A J α ht E a)
    (framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable
    (div_nonneg hK.nonneg (sq_nonneg t)) hB hsup hv hφ).symm

include hs hE in
omit [ConnectedSpace X] in
lemma kernelInputTest_shift_measurable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : VolterraKernel.MeasurableKernel K) (a : TwoForm X) (ha : IsSmooth a)
    (W : ℝ → X → FrameSpace A) (hW : StronglyMeasurable (Function.uncurry W)) :
    StronglyMeasurable (fun p : ℝ × ℝ => kernelInputTest A J α ht E K a (p.1-p.2) (W p.2)) := by
  let := geometricVolume_finite A J α hs ht
  have hkm := kernelTestLinear_measurable A J α hs ht E hE K hK a ha
  have hm : StronglyMeasurable (fun p : (ℝ × ℝ) × X =>
      kernelTestLinear A J α ht E K a (p.1.1-p.1.2) p.2 (W p.1.2 p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hkm.comp_measurable (show Measurable (fun p : (ℝ × ℝ) × X => (p.1.1-p.1.2,p.2)) by fun_prop)).prodMk
        (hW.comp_measurable (measurable_fst.snd.prodMk measurable_snd)))
  exact hm.integral_prod_right

include hs in
omit [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [BorelSpace X] in
lemma kernelInputTest_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A) (a : TwoForm X)
    (t : ℝ) (v : X → FrameSpace A) {B V : ℝ} (hB : 0 ≤ B)
    (hφ : ∀ y, ‖kernelTestLinear A J α ht E K a t y‖ ≤ B) (hv : ∀ y, ‖v y‖ ≤ V) :
    ‖kernelInputTest A J α ht E K a t v‖ ≤ (geometricVolume A J α).real univ*(B*V) := by
  let := geometricVolume_finite A J α hs ht
  calc
    _ ≤ ∫ y : X, B*V ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hφ y) (hv y) (norm_nonneg _) hB)
    _ = _ := by simp [integral_const,smul_eq_mul]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
