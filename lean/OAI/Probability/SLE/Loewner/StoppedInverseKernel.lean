import OAI.Probability.SLE.Loewner.RawRestartRandomTests
import OAI.Probability.SLE.Geometry.StoppedFutureGreen
import OAI.Probability.SLE.Loewner.StoppedInversePaths

namespace OAI

/-! The actual inverse image of the fresh canonical mass has the original
Green remainder kernel in the full filtration after the restart. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

lemma weightedImageMass_add (J : upperHalfPlane → upperHalfPlane) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (μ ν : Measure upperHalfPlane) :
    weightedImageMass J w (μ+ν)=weightedImageMass J w μ+weightedImageMass J w ν := by
  simp only [weightedImageMass,withDensity_add_measure]
  exact Measure.map_add _ _ hJ

lemma weighted_rectangle_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure upperHalfPlane)
    (J : Ω → upperHalfPlane → upperHalfPlane) (hJ : ∀ ω, Measurable (J ω))
    (w : Ω → upperHalfPlane → ℝ≥0∞) (hw : ∀ ω, Measurable (w ω))
    (E : Set Ω) (hE : MeasurableSet E) (A : Set upperHalfPlane) (hA : MeasurableSet A) :
    (∫⁻ ω, ∫⁻ z, w ω z * (E ×ˢ A).indicator (fun _ => 1) (ω,J ω z) ∂μ ω ∂P) =
      ∫⁻ ω in E, weightedImageMass (J ω) (w ω) (μ ω) A ∂P := by
  have he (ω : Ω) :
      (∫⁻ z, w ω z * (E ×ˢ A).indicator (fun _ => 1) (ω,J ω z) ∂μ ω) =
      ∫⁻ x, (E ×ˢ A).indicator (fun _ => 1) (ω,x)
        ∂weightedImageMass (J ω) (w ω) (μ ω) := by
    exact (weightedImageMass_lintegral _ (hJ ω) _ (hw ω) _ _
      ((measurable_const.indicator (hE.prod hA)).comp measurable_prodMk_left)).symm
  simp_rw [he]
  exact past_rectangle_lintegral _ E hE A hA

local instance stoppedKernelDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance stoppedKernelDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
  (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (R : RawCanonicalMass)
  (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
    R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
  (τ : Ω → ℝ≥0)
  (hτ : IsStoppingTime (Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
    (fun ω => (τ ω:WithTop ℝ≥0)))
  (hFresh : ∀ᵐ ω ∂P, ∃ (β : ℝ≥0 → ℂ) (G' F' : ℝ≥0 → ℂ → ℂ),
    IsCapacityTwoWitness (fun t => Real.sqrt κ*B (τ ω+t) ω-Real.sqrt κ*B (τ ω) ω) β G' F')

include C hB hc hκ F hw R he τ hτ hFresh in
theorem CanonicalMass.stoppedFreshMass_green_kernel
    (t : ℝ≥0) (E : Set Ω) (hE : MeasurableSet[shiftedStoppingFiltration hτ t] E) :
    (P.restrict E).bind (stoppedFreshTerminalMass B κ γ G F hw τ hc R) =
      (P.restrict E).bind (stoppedFreshMass B κ γ G F hw τ hc R t)+
      (P.restrict E).bind (fun ω => halfPlaneGreenMeasure κ B γ G (τ ω+t) ω) := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hTm := stoppedFreshTerminalMass_measurable B κ γ G F hw τ hm hc hτ hκ R
  have hNm := (stoppedFreshMass_adapted B κ γ G F hw τ hc R hm hτ hκ).measurable (i := t)
  have hGm : Measurable (fun ω => halfPlaneGreenMeasure κ B γ G (τ ω+t) ω) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
    simp only [halfPlaneGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
      withDensity_apply _ hAI]
    exact (actual_greenDensity_random_time_joint_measurable hBm hc κ γ G F hw
      (fun ω => τ ω+t) (stopping_time_measurable_nnreal (stopping_time_add_nnreal hτ t))).ennreal_ofReal.lintegral_prod_right'
  have hle : hτ.measurableSpace ≤ shiftedStoppingFiltration hτ t :=
    IsStoppingTime.measurableSpace_mono hτ (stopping_time_add_nnreal hτ t)
      (fun ω => WithTop.coe_le_coe.mpr (le_add_of_nonneg_right (show 0 ≤ t from zero_le)))
  have hprod : hτ.measurableSpace.prod (inferInstance : MeasurableSpace upperHalfPlane) ≤
      (shiftedStoppingFiltration hτ t).prod inferInstance :=
    sup_le_sup (MeasurableSpace.comap_mono hle) le_rfl
  have hJ := stoppedMassPoint_measurable B κ γ G F hw τ hm hc hτ
  have hW := stoppedMassWeight_measurable B κ γ G F hw τ hm hc hτ hκ
  have hpair (ω : Ω) : @Measurable upperHalfPlane (Ω × upperHalfPlane) inferInstance
      (hτ.measurableSpace.prod inferInstance) (fun z => (ω,z)) :=
    @measurable_prodMk_left Ω upperHalfPlane hτ.measurableSpace inferInstance ω
  have hJsec (ω : Ω) : Measurable (stoppedMassPoint B κ γ G F hw τ ω) :=
    @Measurable.comp upperHalfPlane (Ω × upperHalfPlane) upperHalfPlane
      inferInstance (hτ.measurableSpace.prod inferInstance) inferInstance
      (fun p => stoppedMassPoint B κ γ G F hw τ p.1 p.2) (fun z => (ω,z)) hJ (hpair ω)
  have hWsec (ω : Ω) : Measurable (stoppedMassWeight B κ F τ ω) :=
    @Measurable.comp upperHalfPlane (Ω × upperHalfPlane) ℝ≥0∞
      inferInstance (hτ.measurableSpace.prod inferInstance) inferInstance
      (fun p => stoppedMassWeight B κ F τ p.1 p.2) (fun z => (ω,z)) hW (hpair ω)
  have hcov := stopped_future_green_covariance B κ γ G F hw τ hm hc hτ hκ hFresh
  have hE' : MeasurableSet E := (shiftedStoppingFiltration hτ).le t _ hE
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA hTm.aemeasurable,Measure.add_apply,
    Measure.bind_apply hA hNm.aemeasurable,Measure.bind_apply hA hGm.aemeasurable]
  let g : Ω × upperHalfPlane → ℝ≥0∞ := fun p => stoppedMassWeight B κ F τ p.1 p.2 *
    (E ×ˢ A).indicator (fun _ => 1) (p.1,stoppedMassPoint B κ γ G F hw τ p.1 p.2)
  have hg : Measurable[(shiftedStoppingFiltration hτ t).prod inferInstance] g :=
    (hW.mono hprod le_rfl).mul
      ((measurable_const.indicator (hE.prod hA)).comp
        (measurable_fst.prodMk (hJ.mono hprod le_rfl)))
  have hh := C.raw_restarted_random_green_test hB hc F hw R he τ hτ t g hg
  change (∫⁻ ω, ∫⁻ z, stoppedMassWeight B κ F τ ω z *
      (E ×ˢ A).indicator (fun _ => 1) (ω,stoppedMassPoint B κ γ G F hw τ ω z)
        ∂(R.terminal (sourceRestartDriverPath B hc τ ω)) ∂P) =
    (∫⁻ ω, ∫⁻ z, stoppedMassWeight B κ F τ ω z *
      (E ×ˢ A).indicator (fun _ => 1) (ω,stoppedMassPoint B κ γ G F hw τ ω z)
        ∂(R.process t (sourceRestartDriverPath B hc τ ω)+
          canonicalGreenMass κ t (sourceRestartDriverPath B hc τ ω)) ∂P) at hh
  rw [weighted_rectangle_lintegral P _ _ hJsec
      _ hWsec E hE' A hA,
    weighted_rectangle_lintegral P _ _ hJsec
      _ hWsec E hE' A hA] at hh
  calc
    _ = ∫⁻ ω in E, weightedImageMass (stoppedMassPoint B κ γ G F hw τ ω)
        (stoppedMassWeight B κ F τ ω)
        (R.process t (sourceRestartDriverPath B hc τ ω)+
          canonicalGreenMass κ t (sourceRestartDriverPath B hc τ ω)) A ∂P := hh
    _ = ∫⁻ ω in E, stoppedFreshMass B κ γ G F hw τ hc R t ω A +
        halfPlaneGreenMeasure κ B γ G (τ ω+t) ω A ∂P := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hcov] with ω hω
      rw [weightedImageMass_add _ (hJsec ω),Measure.add_apply,hω t]
      rfl
    _ = _ := by
      exact lintegral_add_left ((Measure.measurable_coe hA).comp hNm) _

end SLEExactGauge.Multipoint

end

end OAI
