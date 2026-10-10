import OAI.Probability.SLE.Loewner.StoppedInverseMeans
import OAI.Probability.SLE.Mass.RadonProcessAEUniqueness

namespace OAI

/-! The original increment and the transported fresh mass have identical
positive compact tests simultaneously at every finite future time. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance stoppedTestUniqueLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

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
lemma CanonicalMass.stoppedFreshMass_test_indistinguishable
    (hpaths : ∀ᵐ ω ∂P, PositiveMassPaths
      (fun t => stoppedFreshMass B κ γ G F hw τ hc R t ω)
      (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω))
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) :
    ∀ᵐ ω ∂P, ∀ t,
      (∫ z, f z ∂C.process (τ ω+t) ω)-(∫ z, f z ∂C.process (τ ω) ω) =
        ∫ z, f z ∂stoppedFreshMass B κ γ G F hw τ hc R t ω := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hCm := C.original_shifted_adapted τ hτ
  have hNm := stoppedFreshMass_adapted B κ γ G F hw τ hc R hm hτ hκ
  have hTm := stoppedFreshTerminalMass_measurable B κ γ G F hw τ hm hc hτ hκ R
  have hCI (t : ℝ≥0) : Integrable (fun ω => ∫ z, f z ∂C.process (τ ω+t) ω) P := by
    apply positive_kernel_test_integrable P κ _ (hCm.measurable (i := t)) _ f hf
    simpa only [Measure.restrict_univ] using C.original_shifted_mean_le τ hτ t univ
  have hC0I : Integrable (fun ω => ∫ z, f z ∂C.process (τ ω) ω) P := by
    simpa only [add_zero] using hCI 0
  have hNI (t : ℝ≥0) : Integrable
      (fun ω => ∫ z, f z ∂stoppedFreshMass B κ γ G F hw τ hc R t ω) P := by
    apply positive_kernel_test_integrable P κ _ (hNm.measurable (i := t)) _ f hf
    simpa only [Measure.restrict_univ] using
      C.stoppedFreshMass_mean_le hB hc hκ F hw R he τ hτ hFresh t univ
  have hTI : Integrable
      (fun ω => ∫ z, f z ∂stoppedFreshTerminalMass B κ γ G F hw τ hc R ω) P := by
    apply positive_kernel_test_integrable P κ _ hTm _ f hf
    simpa only [Measure.restrict_univ] using
      C.stoppedFreshTerminalMass_mean_le_of_fresh hB hc hκ F hw R he τ hτ hFresh univ
  have hCA : StronglyAdapted (shiftedStoppingFiltration hτ)
      (fun t ω => ∫ z, f z ∂C.process (τ ω+t) ω) := by
    intro t
    exact (@positive_test_integral_measurable Ω (shiftedStoppingFiltration hτ t)
      _ (hCm t) f hf).stronglyMeasurable
  have hC0A : StronglyAdapted (shiftedStoppingFiltration hτ)
      (fun _ ω => ∫ z, f z ∂C.process (τ ω) ω) := by
    intro t
    have h := (hCA 0).mono ((shiftedStoppingFiltration hτ).mono (show 0 ≤ t from zero_le))
    simpa only [add_zero] using h
  have hNA : StronglyAdapted (shiftedStoppingFiltration hτ)
      (fun t ω => ∫ z, f z ∂stoppedFreshMass B κ γ G F hw τ hc R t ω) := by
    intro t
    exact (@positive_test_integral_measurable Ω (shiftedStoppingFiltration hτ t)
      _ (hNm t) f hf).stronglyMeasurable
  have hAI (t : ℝ≥0) : Integrable (fun ω =>
      (∫ z, f z ∂C.process (τ ω+t) ω)-(∫ z, f z ∂C.process (τ ω) ω)) P :=
    (hCI t).sub hC0I
  have hZI : Integrable (fun ω =>
      (∫ z, f z ∂C.rational.terminal ω)-(∫ z, f z ∂C.process (τ ω) ω)) P :=
    (C.uniqueness_terminal_test_integrable f).sub hC0I
  apply increasing_mass_unique_of_terminal_mean
    (fun t ω => (∫ z, f z ∂C.process (τ ω+t) ω)-(∫ z, f z ∂C.process (τ ω) ω))
    (fun t ω => ∫ z, f z ∂stoppedFreshMass B κ γ G F hw τ hc R t ω)
    (fun ω => (∫ z, f z ∂C.rational.terminal ω)-(∫ z, f z ∂C.process (τ ω) ω)-
      (∫ z, f z ∂stoppedFreshTerminalMass B κ γ G F hw τ hc R ω))
    (hZI.sub hTI)
    (hCA.sub hC0A) hNA hAI hNI
  · intro t E hE
    have h := C.stoppedFreshMass_test_cross_mean hB hc hκ F hw R he τ hτ hFresh f hf t E hE
    rw [integral_sub (hAI t).integrableOn (hNI t).integrableOn,
      integral_sub (hCI t).integrableOn hC0I.integrableOn,
      integral_sub hZI.integrableOn hTI.integrableOn,
      integral_sub (C.uniqueness_terminal_test_integrable f).integrableOn hC0I.integrableOn]
    linarith
  · filter_upwards [C.paths] with ω hp
    intro s t hst
    apply sub_le_sub_right
    let := (C.radon (τ ω+t) ω).1
    exact integral_mono_measure (hp.monotone (add_le_add le_rfl hst)) (ae_of_all _ hf) f.integrable
  · filter_upwards [hpaths] with ω hp
    intro s t hst
    let := (hp.radon t).1
    exact integral_mono_measure (hp.monotone hst) (ae_of_all _ hf) f.integrable
  · exact ae_of_all _ (fun ω => by simp only [add_zero,sub_self,Pi.zero_apply])
  · filter_upwards [hpaths] with ω hp
    simp only [hp.zero,integral_zero_measure,Pi.zero_apply]
  · filter_upwards [C.paths,hpaths] with ω hp hq
    exact (((hp.continuous_tests f).comp (continuous_const.add continuous_id)).sub
      continuous_const).sub (hq.continuous_tests f hf)

include C hB hc hκ F hw R he τ hτ hFresh in
/-- Equality of the actual measure increments on one event for every finite
future time, with the unmodified raw fresh functional. -/
theorem CanonicalMass.stoppedFreshMass_indistinguishable
    (hpaths : ∀ᵐ ω ∂P, PositiveMassPaths
      (fun t => stoppedFreshMass B κ γ G F hw τ hc R t ω)
      (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω)) :
    ∀ᵐ ω ∂P, ∀ t,
      C.process (τ ω+t) ω-C.process (τ ω) ω =
        stoppedFreshMass B κ γ G F hw τ hc R t ω := by
  apply random_radon_process_eq_of_positive_tests_ae P (localTestFamily upperHalfPlane)
  · filter_upwards [] with ω
    intro t
    let := (C.radon (τ ω+t) ω).2
    let := halfPlane_sub_finite_on_compacts (C.process (τ ω+t) ω) (C.process (τ ω) ω)
    infer_instance
  · exact hpaths.mono (fun _ h => fun t => (h.radon t).1)
  · intro f hf
    filter_upwards [C.paths,
      C.stoppedFreshMass_test_indistinguishable hB hc hκ F hw R he τ hτ hFresh hpaths f hf]
      with ω hp ht
    intro t
    let := (C.radon (τ ω+t) ω).1
    let := (C.radon (τ ω) ω).1
    rw [integral_halfPlane_sub _ _ (hp.monotone (le_add_of_nonneg_right (show 0 ≤ t from zero_le))) f]
    exact ht t

end SLEExactGauge.Multipoint

end

end OAI
