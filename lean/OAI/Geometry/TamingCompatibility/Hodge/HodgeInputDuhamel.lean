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

include hE in
lemma kernelInputTest_convolution
    (K L : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H C T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C L)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) :
    kernelInputTest A J α ht E (VolterraKernel.convolution (geometricVolume A J α) K L) a t v =
      ∫ s in Ioo 0 t, kernelInputTest A J α ht E K a (t-s)
        (KernelL2.action (geometricVolume A J α) (L s) v) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  have hconv := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0
    (htp.1.le.trans htp.2) K L hK hL
  rw [kernelInputTest_action A J α hs ht E hE _ hconv a ha htp v hvm hv]
  rw [KernelL2.convolution_pairing (geometricVolume A J α) K L hK hL htp v hvm hV hv
    (framePairing A J α ht E a) (framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable hB hφ]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hsp
  have ha' : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hsp.2,(sub_le_self _ hsp.1.le).trans htp.2⟩
  have hb' : s ∈ Ioc 0 T := ⟨hsp.1,hsp.2.le.trans htp.2⟩
  have hr (x : X) := hL.row_int s hb' x
  have hb (x : X) := hL.row s hb' x
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hr hb
  exact (kernelInputTest_action A J α hs ht E hE K hK a ha ha'
    (KernelL2.action (geometricVolume A J α) (L s) v)
    (KernelL2.action_measurable (geometricVolume A J α) (L s)
      (VolterraKernel.kernel_section L hL.measurable s) v hvm)
    (fun x => KernelL2.action_norm (geometricVolume A J α) (L s) v hV hv x (hr x) (hb x))).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.TimeTriangle
open MeasureTheory Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma integral_swap {t : ℝ} (G : ℝ → ℝ → E)
    (hG : StronglyMeasurable (Function.uncurry G)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ s ∈ Ioo 0 t, ∀ u ∈ Ioo s t, ‖G u s‖ ≤ B) :
    (∫ s in Ioo 0 t, ∫ u in Ioo s t, G u s) =
      ∫ u in Ioo 0 t, ∫ s in Ioo 0 u, G u s := by
  let F := fun p : ℝ × ℝ => if p.1 < p.2 then G p.2 p.1 else 0
  have hFm : StronglyMeasurable F :=
    (hG.comp_measurable measurable_swap).piecewise
      (measurableSet_lt measurable_fst measurable_snd) stronglyMeasurable_const
  have hFi : Integrable F ((volume.restrict (Ioo 0 t)).prod (volume.restrict (Ioo 0 t))) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable B
    have hp : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioo 0 t)).prod (volume.restrict (Ioo 0 t)),
        p.1 ∈ Ioo 0 t ∧ p.2 ∈ Ioo 0 t := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact ⟨hs,hu⟩
    filter_upwards [hp] with p hp
    dsimp [F]
    split_ifs with h
    · exact hb p.1 hp.1 p.2 ⟨h,hp.2.2⟩
    · simpa using hB
  have hleft (s : ℝ) (hs : s ∈ Ioo 0 t) :
      (∫ u in Ioo 0 t, F (s,u)) = ∫ u in Ioo s t, G u s := by
    have heq : (Ioi s) ∩ Ioo 0 t = Ioo s t := by ext u; simp only [mem_inter_iff,mem_Ioi,mem_Ioo]; constructor <;> intro h <;> grind
    change (∫ u in Ioo 0 t, (Ioi s).indicator (fun u => G u s) u) = _
    rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,heq]
  have hright (u : ℝ) (hu : u ∈ Ioo 0 t) :
      (∫ s in Ioo 0 t, F (s,u)) = ∫ s in Ioo 0 u, G u s := by
    have heq : (Iio u) ∩ Ioo 0 t = Ioo 0 u := by ext s; simp only [mem_inter_iff,mem_Iio,mem_Ioo]; constructor <;> intro h <;> grind
    change (∫ s in Ioo 0 t, (Iio u).indicator (fun s => G u s) s) = _
    rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,heq]
  calc
    _ = ∫ s in Ioo 0 t, ∫ u in Ioo 0 t, F (s,u) := by
      apply setIntegral_congr_fun measurableSet_Ioo; intro s hs; exact (hleft s hs).symm
    _ = ∫ u in Ioo 0 t, ∫ s in Ioo 0 t, F (s,u) := integral_integral_swap hFi
    _ = _ := setIntegral_congr_fun measurableSet_Ioo hright

end TamingCompatibility.GeometricHilbert.TimeTriangle

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.TimeTriangle
open MeasureTheory Set Filter

lemma integrated_primitive {t : ℝ} (F A : ℝ → ℝ) (G : ℝ → ℝ → ℝ)
    (hF : IntegrableOn F (Ioo 0 t)) (hA : IntegrableOn A (Ioo 0 t))
    (hG : StronglyMeasurable (Function.uncurry G)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ s ∈ Ioo 0 t, ∀ u ∈ Ioo s t, ‖G u s‖ ≤ B)
    (hp : ∀ s ∈ Ioo 0 t, F s-A s = ∫ u in Ioo s t, G u s) :
    (∫ s in Ioo 0 t, F s) = (∫ s in Ioo 0 t, A s) +
      ∫ u in Ioo 0 t, ∫ s in Ioo 0 u, G u s := by
  calc
    _ = (∫ s in Ioo 0 t, A s) + ∫ s in Ioo 0 t, F s-A s := by
      rw [integral_sub hF hA]; ring
    _ = (∫ s in Ioo 0 t, A s) + ∫ s in Ioo 0 t, ∫ u in Ioo s t, G u s := by
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioo hp
    _ = _ := by rw [integral_swap G hG hB hb]

end TamingCompatibility.GeometricHilbert.TimeTriangle

namespace TamingCompatibility.GeometricHilbert.TimeTriangle
open MeasureTheory Set
lemma integral_shift (f : ℝ → ℝ) {s t : ℝ} (hst : s ≤ t) :
    (∫ u in Ioo s t, f (u-s)) = ∫ q in Ioo 0 (t-s), f q := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hst,
    intervalIntegral.integral_comp_sub_right,sub_self,
    intervalIntegral.integral_of_le (sub_nonneg.mpr hst),integral_Ioc_eq_integral_Ioo]
end TamingCompatibility.GeometricHilbert.TimeTriangle

end
end

end

end OAI
