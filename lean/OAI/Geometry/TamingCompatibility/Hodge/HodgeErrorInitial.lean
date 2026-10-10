import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalCorrection
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatBoundL2

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

include hs in
omit [T2Space X] [BorelSpace X] in
lemma kernelWeakAction_bound_of_col
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A) (v : X → FrameSpace A)
    (a : TwoForm X) {C V H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hφ : ∀ x, ‖framePairing A J α ht E a x‖ ≤ C) (hv : ∀ y, ‖v y‖ ≤ V)
    (t : ℝ) (hKi : ∀ y, Integrable (fun x => ‖K t x y‖) (geometricVolume A J α))
    (hKb : ∀ y, (∫ x, ‖K t x y‖ ∂geometricVolume A J α) ≤ H) :
    ‖kernelWeakAction A J α ht E K v a t‖ ≤ (geometricVolume A J α).real univ * (C*V*H) := by
  let := geometricVolume_finite A J α hs ht
  unfold kernelWeakAction
  calc
    _ ≤ ∫ _y : X, C*V*H ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      filter_upwards [] with y
      exact (kernel_pairing_integral_bound A J α ht E a hC hφ _ (v y) (hKi y) (hKb y)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv y) hC) hH)
    _ = _ := by rw [integral_const]; rfl

attribute [local irreducible] framePairing globalLeading globalResidual globalError
variable [ConnectedSpace X] [SecondCountableTopology X]
include hs hE in
lemma globalError_weak_initial : ∃ T : ℝ, 0 < T ∧
    ∀ (v : X → FrameSpace A), Continuous v → ∀ (a : TwoForm X), IsSmooth a →
      Tendsto (kernelWeakAction A J α ht E (globalError J α ht A E T) v a) (𝓝[>] 0) (𝓝 0) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,C,hT,hC,-,-,-,hcol⟩ := globalError_bound J α hs ht A E hE 0
  refine ⟨T,hT,?_⟩
  intro v hv a ha
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  obtain ⟨V,hV⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  have hc : Continuous (fun t : ℝ => (geometricVolume A J α).real univ *
      (B * max V 0 * (t*C))) := by fun_prop
  apply squeeze_zero_norm' (a := fun t : ℝ => (geometricVolume A J α).real univ *
    (B * max V 0 * (t*C)))
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t htp htT
    have hi (y : X) := (hcol t ⟨htp,htT.le⟩ y).1
    have hb (y : X) := (hcol t ⟨htp,htT.le⟩ y).2
    simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
    exact kernelWeakAction_bound_of_col A J α hs ht E _ v a hB (mul_nonneg htp.le hC) hφ
      (fun y => (hV y (mem_univ y)).trans (le_max_left _ _)) t hi hb
  · simpa only [zero_mul,mul_zero] using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)

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

attribute [local irreducible] framePairing globalLeading globalResidual

include hE in
lemma globalError_weak_initial_of_bounds {T L C : ℝ} (hT : 0 < T)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E))
    (hC : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C (globalCorrection J α ht A E T))
    (v : X → FrameSpace A) (hv : Continuous v) (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (kernelWeakAction A J α ht E (globalError J α ht A E T) v a) (𝓝[>] 0) (𝓝 0) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  obtain ⟨V,hV⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  have hz := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (geometricVolume A J α).real univ *
    (B*(max V 0)*(L*C))) (𝓝[>] 0) (𝓝 _)).mul
      (nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0))
  simp only [mul_zero] at hz
  apply squeeze_zero_norm' _ hz
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t htp htT
  have hc (y : X) := VolterraKernel.convolution_col (geometricVolume A J α) 0 _ _ hL hC ⟨htp,htT.le⟩ y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hc
  have hh := kernelWeakAction_bound_of_col A J α hs ht E _ v a hB
    (mul_nonneg (mul_nonneg htp.le hL.nonneg) hC.nonneg) hφ
    (fun y => (hV y (mem_univ y)).trans (le_max_left V 0)) t
    (fun y => (hc y).1) (fun y => (hc y).2)
  exact hh.trans_eq (by ring)

include hE in

lemma globalCandidate_L2_realization : ∃ T : ℝ, 0 < T ∧
    ∀ (v : X → FrameSpace A), Continuous v →
    ∃ (f : L2 A J α hs ht true) (U : ℝ → L2 A J α hs ht true) (M : ℝ),
      0 ≤ M ∧ U 0 = f ∧ (∀ t ∈ Icc 0 T, ‖U t‖ ≤ M) ∧
      (∀ a : PreL2 A J α hs ht true,
        ⟪f,smoothL2 A J α hs ht true a⟫ =
          ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
        ⟪U t,smoothL2 A J α hs ht true a⟫ =
          kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
          kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) ∧
      (∀ a : PreL2 A J α hs ht true,
        Tendsto (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (𝓝[>] 0)
          (𝓝 ⟪f,smoothL2 A J α hs ht true a⟫)) := by
  classical
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,C,hT,hL,hC,-⟩ := globalCorrection_bound J α hs ht A E hE 0
  have hErr := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ _ hL hC
  refine ⟨T,hT,?_⟩
  intro v hv
  obtain ⟨V₀,hV₀⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let V := max V₀ 0
  have hV : 0 ≤ V := le_max_right _ _
  have hvb (y : X) : ‖v y‖ ≤ V := (hV₀ y (mem_univ y)).trans (le_max_left _ _)
  let f := boundedFrameSection A J α hs ht E hE v hv.aestronglyMeasurable V hV
    (Eventually.of_forall hvb)
  let P := heatBoundL2 A J α hs ht E hE _ T L hL v hv.stronglyMeasurable V hV hvb
  let Q := heatBoundL2 A J α hs ht E hE _ T (4*T*L*C) hErr v hv.stronglyMeasurable V hV hvb
  let U := fun t => if t=0 then f else P t+Q t
  let M := ‖f‖ + frameNormConstant A J α hs ht E hE*(L*V) +
    frameNormConstant A J α hs ht E hE*((4*T*L*C)*V)
  have hLn := mul_nonneg (frameNormConstant_nonneg A J α hs ht E hE) (mul_nonneg hL.nonneg hV)
  have hQn := mul_nonneg (frameNormConstant_nonneg A J α hs ht E hE) (mul_nonneg hErr.nonneg hV)
  have hf (a : PreL2 A J α hs ht true) : ⟪f,smoothL2 A J α hs ht true a⟫ =
      ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α :=
    boundedFrameSection_pairing A J α hs ht E hE v hv.aestronglyMeasurable V hV
      (Eventually.of_forall hvb) a
  have hp (a : PreL2 A J α hs ht true) (t : ℝ) (htp : t ∈ Ioc 0 T) :
      ⟪U t,smoothL2 A J α hs ht true a⟫ =
        kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
        kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t := by
    rw [show U t = P t+Q t by simp [U,htp.1.ne'],inner_add_left]
    rw [heatBoundL2_pairing A J α hs ht E hE _ T L hL v hv.stronglyMeasurable V hV hvb a htp,
      heatBoundL2_pairing A J α hs ht E hE _ T _ hErr v hv.stronglyMeasurable V hV hvb a htp]
    rfl
  refine ⟨f,U,M,by dsimp only [M]; positivity,by simp [U],?_,hf,hp,?_⟩
  · intro t _ht
    by_cases hz : t=0
    · simpa [U,hz,M] using (show ‖f‖ ≤ M by dsimp only [M]; linarith)
    · rw [show U t = P t+Q t by simp [U,hz]]
      have hP := heatBoundL2_norm A J α hs ht E hE _ T L hL v hv.stronglyMeasurable V hV hvb t
      have hQ := heatBoundL2_norm A J α hs ht E hE _ T _ hErr v hv.stronglyMeasurable V hV hvb t
      exact (norm_add_le _ _).trans (by dsimp only [M]; linarith [norm_nonneg f])
  · intro a
    have hh := (kernelWeakAction_leading_initial A J α hs ht E hE v hv a.val a.property).add
      (globalError_weak_initial_of_bounds A J α hs ht E hE hT hL hC v hv a.val a.property)
    rw [add_zero,← hf a] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t htp htT
    exact (hp a t ⟨htp,htT.le⟩).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
