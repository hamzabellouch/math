import OAI.Probability.SLE.Geometry.PositiveKernelTests
import OAI.Probability.SLE.Loewner.StoppedInversePaths
import OAI.Probability.SLE.Mass.RadonProcessAEUniqueness

namespace OAI

/-! The uniqueness step used to compare canonical mass with its spatial
and temporal dilation. Only the positive compact tests of the two Green
remainder kernels are required. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge.Multipoint

local instance greenMassUniqueLocallyCompact : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {ℱ : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure P] in
lemma restricted_kernel_mean_le
    (μ : Ω → Measure upperHalfPlane) (hm : Measurable μ)
    (hb : P.bind μ ≤ initialGreenMeasure κ) (E : Set Ω) :
    (P.restrict E).bind μ ≤ initialGreenMeasure κ :=
  (restricted_bind_le_of_ae_le P μ μ hm hm (ae_of_all _ (fun _ => le_rfl)) E).trans hb

lemma positive_mass_process_eq_of_cross_kernel
    (A B : ℝ≥0 → Ω → Measure upperHalfPlane) (ZA ZB : Ω → Measure upperHalfPlane)
    (hA : Adapted ℱ A) (hB : Adapted ℱ B) (hZA : Measurable ZA) (hZB : Measurable ZB)
    (hAb : ∀ t, P.bind (A t) ≤ initialGreenMeasure κ)
    (hBb : ∀ t, P.bind (B t) ≤ initialGreenMeasure κ)
    (hZAb : P.bind ZA ≤ initialGreenMeasure κ) (hZBb : P.bind ZB ≤ initialGreenMeasure κ)
    (hpA : ∀ᵐ ω ∂P, PositiveMassPaths (fun t => A t ω) (ZA ω))
    (hpB : ∀ᵐ ω ∂P, PositiveMassPaths (fun t => B t ω) (ZB ω))
    (hcross : ∀ t E, MeasurableSet[ℱ t] E →
      (P.restrict E).bind ZA+(P.restrict E).bind (B t)=
        (P.restrict E).bind ZB+(P.restrict E).bind (A t)) :
    ∀ᵐ ω ∂P, ∀ t, A t ω=B t ω := by
  apply random_radon_process_eq_of_positive_tests_ae P (localTestFamily upperHalfPlane) A B
    (hpA.mono (fun _ h => fun t => (h.radon t).1))
    (hpB.mono (fun _ h => fun t => (h.radon t).1))
  intro f hf
  have hAm (t : ℝ≥0) := hA.measurable (i:=t)
  have hBm (t : ℝ≥0) := hB.measurable (i:=t)
  have hAI (t : ℝ≥0) := positive_kernel_test_integrable P κ (A t) (hAm t) (hAb t) f hf
  have hBI (t : ℝ≥0) := positive_kernel_test_integrable P κ (B t) (hBm t) (hBb t) f hf
  have hZAI := positive_kernel_test_integrable P κ ZA hZA hZAb f hf
  have hZBI := positive_kernel_test_integrable P κ ZB hZB hZBb f hf
  have hAA : StronglyAdapted ℱ (fun t ω => ∫ z, f z ∂A t ω) := fun t =>
    (@positive_test_integral_measurable Ω (ℱ t) (A t) (hA t) f hf).stronglyMeasurable
  have hBA : StronglyAdapted ℱ (fun t ω => ∫ z, f z ∂B t ω) := fun t =>
    (@positive_test_integral_measurable Ω (ℱ t) (B t) (hB t) f hf).stronglyMeasurable
  apply increasing_mass_unique_of_terminal_mean
    (fun t ω => ∫ z, f z ∂A t ω) (fun t ω => ∫ z, f z ∂B t ω)
    (fun ω => (∫ z, f z ∂ZA ω)-(∫ z, f z ∂ZB ω)) (hZAI.sub hZBI)
    hAA hBA hAI hBI
  · intro t E hE
    let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
    have ha := restricted_kernel_mean_le (A t) (hAm t) (hAb t) E
    have hb := restricted_kernel_mean_le (B t) (hBm t) (hBb t) E
    have hza := restricted_kernel_mean_le ZA hZA hZAb E
    have hzb := restricted_kernel_mean_le ZB hZB hZBb E
    have h := congrArg (fun μ : Measure upperHalfPlane => ∫ z, f z ∂μ) (hcross t E hE)
    rw [integral_add_measure (f.integrable.mono_measure hza) (f.integrable.mono_measure hb),
      integral_add_measure (f.integrable.mono_measure hzb) (f.integrable.mono_measure ha),
      ← positive_kernel_integral_bind (P.restrict E) κ ZA hZA hza f hf,
      ← positive_kernel_integral_bind (P.restrict E) κ (B t) (hBm t) hb f hf,
      ← positive_kernel_integral_bind (P.restrict E) κ ZB hZB hzb f hf,
      ← positive_kernel_integral_bind (P.restrict E) κ (A t) (hAm t) ha f hf] at h
    rw [integral_sub (hAI t).integrableOn (hBI t).integrableOn,
      integral_sub hZAI.integrableOn hZBI.integrableOn]
    linarith
  · filter_upwards [hpA] with ω hp
    intro s t hst
    let := (hp.radon t).1
    exact integral_mono_measure (hp.monotone hst) (ae_of_all _ hf) f.integrable
  · filter_upwards [hpB] with ω hp
    intro s t hst
    let := (hp.radon t).1
    exact integral_mono_measure (hp.monotone hst) (ae_of_all _ hf) f.integrable
  · filter_upwards [hpA] with ω hp
    simp only [hp.zero,integral_zero_measure,Pi.zero_apply]
  · filter_upwards [hpB] with ω hp
    simp only [hp.zero,integral_zero_measure,Pi.zero_apply]
  · filter_upwards [hpA,hpB] with ω ha hb
    exact (ha.continuous_tests f hf).sub (hb.continuous_tests f hf)

end SLEExactGauge.Multipoint

end

end OAI
