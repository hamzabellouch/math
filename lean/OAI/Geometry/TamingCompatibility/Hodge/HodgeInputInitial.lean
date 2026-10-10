import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeGlobalHeatBound

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] [BorelSpace X] in
lemma kernel_pairing_integral_bound (a : TwoForm X) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ x, ‖framePairing A J α ht E a x‖ ≤ C)
    (K : X → FrameSpace A →L[ℝ] FrameSpace A) (v : FrameSpace A) {H : ℝ}
    (hKi : Integrable (fun x => ‖K x‖) (geometricVolume A J α))
    (hKb : (∫ x, ‖K x‖ ∂geometricVolume A J α) ≤ H) :
    ‖∫ x, framePairing A J α ht E a x (K x v) ∂geometricVolume A J α‖ ≤ C*‖v‖*H := by
  calc
    _ ≤ ∫ x, (C*‖v‖)*‖K x‖ ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (hKi.const_mul _) (Filter.Eventually.of_forall _)
      intro x
      calc
        _ ≤ ‖framePairing A J α ht E a x‖*‖K x v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C*(‖K x‖*‖v‖) := mul_le_mul (hφ x) (ContinuousLinearMap.le_opNorm _ _)
          (norm_nonneg _) hC
        _ = _ := by ring
    _ = (C*‖v‖)*(∫ x, ‖K x‖ ∂geometricVolume A J α) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hKb (mul_nonneg hC (norm_nonneg _))

include hs hE in
lemma kernel_leading_pairing_initial (y : X) (v : FrameSpace A)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ x, framePairing A J α ht E a x
      (globalLeading J α ht A E t x y v) ∂geometricVolume A J α)
      (𝓝[>] 0) (𝓝 (framePairing A J α ht E a y v)) := by
  have hh := leadingKernelForm_initial A J α hs ht E hE y v a ha
  rw [← framePairing_apply] at hh
  simp_rw [leadingKernelForm_pairing A J α ht E hE] at hh
  exact hh

attribute [local irreducible] framePairing globalLeading globalResidual

variable [ConnectedSpace X] [SecondCountableTopology X]
include hs hE in
lemma kernelWeakAction_leading_initial (v : X → FrameSpace A) (hv : Continuous v)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (kernelWeakAction A J α ht E (globalLeading J α ht A E) v a)
      (𝓝[>] 0) (𝓝 (∫ y, framePairing A J α ht E a y (v y) ∂geometricVolume A J α)) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨C,hC,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  obtain ⟨V,hV⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  obtain ⟨H,hH⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  have hc := kernel_pairing_integral_continuousOn A J α hs ht E hE _
    (fun _ hp x y => globalLeading_continuousAt A J α hs ht E hE hp x y) v hv a ha
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [self_mem_nhdsWithin] with t htpos
    exact (continuousOn_univ.mp (hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => htpos))).aestronglyMeasurable
  · refine ⟨C*(max V 0)*H, ?_⟩
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t htp ht1
    filter_upwards [] with y
    have hi := hH.col_int t ⟨htp,ht1.le⟩ y
    have hb := hH.col t ⟨htp,ht1.le⟩ y
    simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
    exact (kernel_pairing_integral_bound A J α ht E a hC hφ _ (v y) hi hb).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((hV y (mem_univ y)).trans (le_max_left _ _)) hC) hH.nonneg)
  · filter_upwards [] with y
    exact kernel_leading_pairing_initial A J α hs ht E hE y (v y) a ha

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

def kernelTestSlice (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (y : X) (v : FrameSpace A) (a : TwoForm X) (t : ℝ) : ℝ :=
  ∫ x, framePairing A J α ht E a x (K t x y v) ∂geometricVolume A J α

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] in
lemma kernelTestSlice_continuousOn
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : ∀ t, 0 < t → ∀ x y, ContinuousAt (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2) (t,x,y))
    (y : X) (v : FrameSpace A) (a : TwoForm X) (ha : IsSmooth a) :
    ContinuousOn (kernelTestSlice A J α ht E K y v a) (Ioi 0) := by
  have hh := kernel_pairing_integral_continuousOn A J α hs ht E hE K hK
    (fun _ => v) continuous_const a ha
  apply hh.comp (continuous_id.prodMk continuous_const).continuousOn
  exact fun _ hp => hp

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma kernelTestSlice_uniform_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H : ℝ}
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 1 H K)
    (a : TwoForm X) (ha : IsSmooth a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 1, ∀ y v,
      ‖kernelTestSlice A J α ht E K y v a t‖ ≤ C*‖v‖ := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  refine ⟨B*H,mul_nonneg hB hK.nonneg,?_⟩
  intro t hp y v
  have hi := hK.col_int t hp y
  have hb := hK.col t hp y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
  exact (kernel_pairing_integral_bound A J α ht E a hB hφ _ v hi hb).trans_eq (by ring)

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma leading_time_primitive (y : X) (v : FrameSpace A)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in (0:ℝ)..t,
      kernelTestSlice A J α ht E (globalResidual J α ht A E) y v a.val s -
      kernelTestSlice A J α ht E (globalLeading J α ht A E) y v
        (hodgeLaplacian A J α hs ht a).val s) =
    kernelTestSlice A J α ht E (globalLeading J α ht A E) y v a.val t -
      framePairing A J α ht E a.val y v := by
  let := geometricMetricSpace J α hs ht
  let F := kernelTestSlice A J α ht E (globalLeading J α ht A E) y v a.val
  let G := fun s => kernelTestSlice A J α ht E (globalResidual J α ht A E) y v a.val s -
    kernelTestSlice A J α ht E (globalLeading J α ht A E) y v
      (hodgeLaplacian A J α hs ht a).val s
  have hd (s : ℝ) (hp : 0 < s) : HasDerivAt F (G s) s :=
    kernel_leading_pairing_hasDerivAt A J α hs ht E hE y v a hp
  have hc : ContinuousOn G (Ioi 0) :=
    (kernelTestSlice_continuousOn A J α hs ht E hE _
      (fun _ hp x y => globalResidual_continuousAt A J α hs ht E hE hp x y) y v a.val a.property).sub
    (kernelTestSlice_continuousOn A J α hs ht E hE _
      (fun _ hp x y => globalLeading_continuousAt A J α hs ht E hE hp x y) y v
      (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property)
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  obtain ⟨B,hB,hRb⟩ := kernelTestSlice_uniform_bound A J α hs ht E hE _ hR a.val a.property
  obtain ⟨C,hC,hLb⟩ := kernelTestSlice_uniform_bound A J α hs ht E hE _ hL
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property
  have hi : IntervalIntegrable G volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le htp.le).mpr
    apply IntegrableOn.of_bound (by simp) ((hc.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo)
      ((B+C)*‖v‖)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs'
    have hp : s ∈ Ioc 0 1 := ⟨hs'.1,hs'.2.le.trans ht1⟩
    exact (norm_sub_le _ _).trans ((add_le_add (hRb s hp y v) (hLb s hp y v)).trans_eq (by ring))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto htp
    (fun s hp => hd s hp.1) hi
    (kernel_leading_pairing_initial A J α hs ht E hE y v a.val a.property)
    ((hd t htp).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
