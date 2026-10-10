import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeBoundedSection

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelL2
open Set Filter MeasureTheory
open scoped Topology
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X) [IsFiniteMeasure μ]

def action (K : X → X → F →L[ℝ] F) (v : X → F) (x : X) : F := ∫ y, K x y (v y) ∂μ

omit [CompleteSpace F] in
lemma applied_measurable (K : X → X → F →L[ℝ] F)
    (hK : StronglyMeasurable (Function.uncurry K)) (v : X → F) (hv : StronglyMeasurable v) :
    StronglyMeasurable (fun p : X × X => K p.1 p.2 (v p.2)) :=
  (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
    (hK.prodMk (hv.comp_measurable measurable_snd))

omit [CompleteSpace F] in
lemma action_measurable (K : X → X → F →L[ℝ] F)
    (hK : StronglyMeasurable (Function.uncurry K)) (v : X → F) (hv : StronglyMeasurable v) :
    StronglyMeasurable (action μ K v) := (applied_measurable K hK v hv).integral_prod_right

omit [IsFiniteMeasure μ] [CompleteSpace F] in
lemma action_integrable (K : X → X → F →L[ℝ] F)
    (hK : StronglyMeasurable (Function.uncurry K)) (v : X → F) (hvm : StronglyMeasurable v)
    {V : ℝ} (hv : ∀ y, ‖v y‖ ≤ V) (x : X)
    (hKi : Integrable (fun y => ‖K x y‖) μ) : Integrable (fun y => K x y (v y)) μ := by
  apply (hKi.mul_const V).mono'
    (((applied_measurable K hK v hvm).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [] with y
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _))

omit [CompleteSpace F] [IsFiniteMeasure μ] in
lemma action_norm (K : X → X → F →L[ℝ] F) (v : X → F) {V H : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (x : X) (hKi : Integrable (fun y => ‖K x y‖) μ)
    (hKb : (∫ y, ‖K x y‖ ∂μ) ≤ H) : ‖action μ K v x‖ ≤ H*V := by
  calc
    _ ≤ ∫ y, ‖K x y‖*V ∂μ := by
      apply norm_integral_le_of_norm_le (hKi.mul_const _) (Eventually.of_forall _)
      intro y
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _))
    _ = (∫ y, ‖K x y‖ ∂μ)*V := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hKb hV

lemma action_test_swap (K : X → X → F →L[ℝ] F)
    (hK : StronglyMeasurable (Function.uncurry K)) (v : X → F) (hvm : StronglyMeasurable v)
    (φ : X → F →L[ℝ] ℝ) (hφm : StronglyMeasurable φ)
    {M V C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hKb : ∀ x y, ‖K x y‖ ≤ M) (hv : ∀ y, ‖v y‖ ≤ V) (hφ : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, φ x (action μ K v x) ∂μ) = ∫ y, ∫ x, φ x (K x y (v y)) ∂μ ∂μ := by
  have hbound (x y : X) : ‖K x y (v y)‖ ≤ M*V :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hKb x y) (hv y) (norm_nonneg _) hM)
  have hm := applied_measurable K hK v hvm
  have htm : StronglyMeasurable (fun p : X × X => φ p.1 (K p.1 p.2 (v p.2))) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hφm.comp_measurable measurable_fst).prodMk hm)
  have hi (x : X) : Integrable (fun y => K x y (v y)) μ := by
    apply (integrable_const (M*V)).mono'
      ((hm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    exact Eventually.of_forall (hbound x)
  have ht : Integrable (fun p : X × X => φ p.1 (K p.1 p.2 (v p.2))) (μ.prod μ) := by
    apply (integrable_const (C*(M*V))).mono' htm.aestronglyMeasurable
    filter_upwards [] with p
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hφ _) (hbound _ _) (norm_nonneg _) hC)
  calc
    _ = ∫ x, ∫ y, φ x (K x y (v y)) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact ((φ x).integral_comp_comm (hi x)).symm
    _ = _ := integral_integral_swap ht

end TamingCompatibility.GeometricHilbert.KernelL2

end
end

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

def frameNormConstant : ℝ := frameMassBound A *
  ∑ p : A.centers, ∑ j : Fin 6, ‖globalFramePreL2 A J α hs ht E hE p j‖

lemma frameNormConstant_nonneg : 0 ≤ frameNormConstant A J α hs ht E hE :=
  mul_nonneg (frameMassBound_nonneg A) (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

def kernelSectionL2 (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hKm : StronglyMeasurable (Function.uncurry K))
    (H : ℝ) (hH : 0 ≤ H)
    (hKi : ∀ x, Integrable (fun y => ‖K x y‖) (geometricVolume A J α))
    (hKb : ∀ x, (∫ y, ‖K x y‖ ∂geometricVolume A J α) ≤ H)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V) : L2 A J α hs ht true := by
  let := geometricVolume_finite A J α hs ht
  exact boundedFrameSection A J α hs ht E hE
    (KernelL2.action (geometricVolume A J α) K v)
    ((KernelL2.action_measurable _ K hKm v hvm).aestronglyMeasurable)
    (H*V) (mul_nonneg hH hV)
    (Eventually.of_forall (fun x => KernelL2.action_norm _ K v hV hv x (hKi x) (hKb x)))

lemma kernelSectionL2_norm (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hKm : StronglyMeasurable (Function.uncurry K))
    (H : ℝ) (hH : 0 ≤ H)
    (hKi : ∀ x, Integrable (fun y => ‖K x y‖) (geometricVolume A J α))
    (hKb : ∀ x, (∫ y, ‖K x y‖ ∂geometricVolume A J α) ≤ H)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V) :
    ‖kernelSectionL2 A J α hs ht E hE K hKm H hH hKi hKb v hvm V hV hv‖ ≤
      frameNormConstant A J α hs ht E hE * (H*V) := by
  unfold kernelSectionL2 frameNormConstant
  apply boundedFrameSection_norm

lemma kernelSectionL2_pairing (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hKm : StronglyMeasurable (Function.uncurry K))
    (H : ℝ) (hH : 0 ≤ H)
    (hKi : ∀ x, Integrable (fun y => ‖K x y‖) (geometricVolume A J α))
    (hKb : ∀ x, (∫ y, ‖K x y‖ ∂geometricVolume A J α) ≤ H)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V)
    (M : ℝ) (hM : 0 ≤ M) (hsup : ∀ x y, ‖K x y‖ ≤ M)
    (a : PreL2 A J α hs ht true) :
    ⟪kernelSectionL2 A J α hs ht E hE K hKm H hH hKi hKb v hvm V hV hv,
      smoothL2 A J α hs ht true a⟫ =
      ∫ y, ∫ x, framePairing A J α ht E a.val x (K x y (v y)) ∂geometricVolume A J α ∂geometricVolume A J α := by
  let := geometricVolume_finite A J α hs ht
  obtain ⟨C,hC,hφ⟩ := framePairing_bound A J α hs ht E hE a.val a.property
  rw [kernelSectionL2,boundedFrameSection_pairing]
  exact KernelL2.action_test_swap _ K hKm v hvm _
    (framePairing_continuous A J α hs ht E hE a.val a.property).stronglyMeasurable hM hC hsup hv hφ

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
