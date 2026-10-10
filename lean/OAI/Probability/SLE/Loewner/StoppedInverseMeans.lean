import OAI.Probability.SLE.Loewner.StoppedInverseKernel
import OAI.Probability.SLE.Mass.OriginalShiftedMass
import OAI.Probability.SLE.Geometry.PositiveKernelTests

namespace OAI

/-! The two increment candidates have the same remaining conditional
potential and integrable positive compact tests. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

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
lemma CanonicalMass.stoppedFreshMass_cross_kernel
    (t : ℝ≥0) (E : Set Ω) (hE : MeasurableSet[shiftedStoppingFiltration hτ t] E) :
    (P.restrict E).bind C.rational.terminal+
        (P.restrict E).bind (stoppedFreshMass B κ γ G F hw τ hc R t) =
      (P.restrict E).bind (stoppedFreshTerminalMass B κ γ G F hw τ hc R)+
        (P.restrict E).bind (fun ω => C.process (τ ω+t) ω) := by
  rw [C.original_shifted_green_kernel τ hτ t E hE,
    C.stoppedFreshMass_green_kernel hB hc hκ F hw R he τ hτ hFresh t E hE]
  ac_rfl

include C hB hc hκ F hw R he τ hτ hFresh in
lemma CanonicalMass.stoppedFreshMass_mean_le (t : ℝ≥0) (E : Set Ω) :
    (P.restrict E).bind (stoppedFreshMass B κ γ G F hw τ hc R t) ≤ initialGreenMeasure κ := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hNm := (stoppedFreshMass_adapted B κ γ G F hw τ hc R hm hτ hκ).measurable (i := t)
  have hT := C.stoppedFreshTerminalMass_kernel hB hc hκ F hw τ hτ R
    (he.mono fun _ h => h.2) hFresh univ MeasurableSet.univ
  have hK := C.stoppedFreshMass_green_kernel hB hc hκ F hw R he τ hτ hFresh
    t univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at hT hK
  have hTmean : P.bind (stoppedFreshTerminalMass B κ γ G F hw τ hc R) ≤ initialGreenMeasure κ := by
    rw [hT]
    exact C.green_at_finite_stop_mean_le τ hτ
  refine (restricted_bind_le_of_ae_le P _ _ hNm hNm (ae_of_all _ (fun _ => le_rfl)) E).trans ?_
  rw [hK] at hTmean
  exact (show P.bind (stoppedFreshMass B κ γ G F hw τ hc R t) ≤
      P.bind (stoppedFreshMass B κ γ G F hw τ hc R t)+
        P.bind (fun ω => halfPlaneGreenMeasure κ B γ G (τ ω+t) ω) from Measure.le_add_right le_rfl).trans hTmean

include C hB hc hκ F hw R he τ hτ hFresh in
lemma CanonicalMass.stoppedFreshTerminalMass_mean_le_of_fresh (E : Set Ω) :
    (P.restrict E).bind (stoppedFreshTerminalMass B κ γ G F hw τ hc R) ≤ initialGreenMeasure κ := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hTm := stoppedFreshTerminalMass_measurable B κ γ G F hw τ hm hc hτ hκ R
  have hT := C.stoppedFreshTerminalMass_kernel hB hc hκ F hw τ hτ R
    (he.mono fun _ h => h.2) hFresh univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at hT
  refine (restricted_bind_le_of_ae_le P _ _ hTm hTm (ae_of_all _ (fun _ => le_rfl)) E).trans ?_
  rw [hT]
  exact C.green_at_finite_stop_mean_le τ hτ

include C hB hc hκ F hw R he τ hτ hFresh in
lemma CanonicalMass.stoppedFreshMass_test_cross_mean
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z)
    (t : ℝ≥0) (E : Set Ω) (hE : MeasurableSet[shiftedStoppingFiltration hτ t] E) :
    (∫ ω in E, ∫ z, f z ∂C.rational.terminal ω ∂P)+
        (∫ ω in E, ∫ z, f z ∂stoppedFreshMass B κ γ G F hw τ hc R t ω ∂P) =
      (∫ ω in E, ∫ z, f z ∂stoppedFreshTerminalMass B κ γ G F hw τ hc R ω ∂P)+
        (∫ ω in E, ∫ z, f z ∂C.process (τ ω+t) ω ∂P) := by
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hTm := stoppedFreshTerminalMass_measurable B κ γ G F hw τ hm hc hτ hκ R
  have hNm := (stoppedFreshMass_adapted B κ γ G F hw τ hc R hm hτ hκ).measurable (i := t)
  have hCm := (C.original_shifted_adapted τ hτ).measurable (i := t)
  have hCT := C.uniqueness_terminal_mean_le E
  have hNT := C.stoppedFreshTerminalMass_mean_le_of_fresh hB hc hκ F hw R he τ hτ hFresh E
  have hN := C.stoppedFreshMass_mean_le hB hc hκ F hw R he τ hτ hFresh t E
  have hC := C.original_shifted_mean_le τ hτ t E
  have h := congrArg (fun μ : Measure upperHalfPlane => ∫ z, f z ∂μ)
    (C.stoppedFreshMass_cross_kernel hB hc hκ F hw R he τ hτ hFresh t E hE)
  rw [integral_add_measure (f.integrable.mono_measure hCT) (f.integrable.mono_measure hN),
    integral_add_measure (f.integrable.mono_measure hNT) (f.integrable.mono_measure hC)] at h
  rw [← positive_kernel_integral_bind (P.restrict E) κ C.rational.terminal
      C.rational.terminal_measurable hCT f hf,
    ← positive_kernel_integral_bind (P.restrict E) κ _ hNm hN f hf,
    ← positive_kernel_integral_bind (P.restrict E) κ _ hTm hNT f hf,
    ← positive_kernel_integral_bind (P.restrict E) κ _ hCm hC f hf] at h
  exact h

end SLEExactGauge.Multipoint

end

end OAI
