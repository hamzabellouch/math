import OAI.Probability.SLE.Mass.CanonicalMassConstruction
import OAI.Probability.SLE.Mass.RadonTerminalUniqueness

namespace OAI

/-! The constructed canonical mass does not depend on the convex extraction.
The uniqueness argument uses only integrable terminal compact tests and the
conditional remainder kernel, rather than second moments of a competitor. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

namespace CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma uniqueness_process_mean_le (t : ℝ≥0) (E : Set Ω) :
    (P.restrict E).bind (C.process t) ≤ initialGreenMeasure κ := by
  have hdom : ∀ᵐ ω ∂P, C.process t ω ≤ C.rational.terminal ω :=
    C.paths.mono (fun _ h => h.dominated t)
  have h := restricted_bind_le_of_ae_le P (C.process t) C.rational.terminal
    (C.progressive.adapted.measurable (i := t)) C.rational.terminal_measurable hdom E
  rwa [C.rational.mean] at h

lemma uniqueness_terminal_mean_le (E : Set Ω) :
    (P.restrict E).bind C.rational.terminal ≤ initialGreenMeasure κ := by
  have h := restricted_bind_le_of_ae_le P C.rational.terminal C.rational.terminal
    C.rational.terminal_measurable C.rational.terminal_measurable (ae_of_all _ (fun _ => le_rfl)) E
  rwa [C.rational.mean] at h

lemma uniqueness_test_integrable (t : ℝ≥0) (f : C_c(upperHalfPlane,ℝ)) :
    Integrable (fun ω => ∫ z, f z ∂C.process t ω) P := by
  let (ω : Ω) : (C.process t ω).Regular := (C.radon t ω).1
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  apply (integrable_integral_bind_of_sections P (C.process t)
    (C.progressive.adapted.measurable (i := t)) f f.continuous.measurable
    (fun _ => f.integrable) ?_).1
  have hfI : Integrable f (initialGreenMeasure κ) := f.integrable
  exact hfI.mono_measure (by
    simpa only [Measure.restrict_univ] using C.uniqueness_process_mean_le t univ)

lemma uniqueness_terminal_test_integrable (f : C_c(upperHalfPlane,ℝ)) :
    Integrable (fun ω => ∫ z, f z ∂C.rational.terminal ω) P := by
  let (ω : Ω) : (C.rational.terminal ω).Regular := (C.rational.terminal_radon ω).1
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  apply (integrable_integral_bind_of_sections P C.rational.terminal C.rational.terminal_measurable
    f f.continuous.measurable (fun _ => f.integrable) ?_).1
  rw [C.rational.mean]
  exact f.integrable

lemma uniqueness_test_adapted (f : C_c(upperHalfPlane,ℝ)) :
    StronglyAdapted (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable))
      (fun t ω => ∫ z, f z ∂C.process t ω) := by
  intro t
  exact (@measurable_halfPlane_compact_test_integral Ω
    ((Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) t)
    (C.process t)
    (C.progressive.adapted t) (fun ω => (C.radon t ω).1) f).stronglyMeasurable

lemma uniqueness_cross_mean (D : CanonicalMass P κ B hBm γ G)
    (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable) t] E) :
    (P.restrict E).bind C.rational.terminal+(P.restrict E).bind (D.process t) =
      (P.restrict E).bind D.rational.terminal+(P.restrict E).bind (C.process t) := by
  let ℱ := Filtration.natural B (fun r =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)
  have hS : IsStoppingTime ℱ (fun _ : Ω => (t:WithTop ℝ≥0)) := isStoppingTime_const ℱ t
  have hES : MeasurableSet[hS.measurableSpace] E := by
    change MeasurableSet[(isStoppingTime_const ℱ t).measurableSpace] E
    rw [IsStoppingTime.measurableSpace_const]
    exact hE
  have hc := C.kernel (fun _ => (t:WithTop ℝ≥0)) hS E hES
  have hd := D.kernel (fun _ => (t:WithTop ℝ≥0)) hS E hES
  have hfinite : (t:WithTop ℝ≥0) < ∞ := WithTop.coe_lt_top t
  have heC : (fun ω => extendedCanonicalMass C.process C.rational.terminal
      ((t:WithTop ℝ≥0):ℝ≥0∞) ω) = C.process t := by
    funext ω
    unfold extendedCanonicalMass
    split_ifs with ht
    · congr 1
    · exact (ht hfinite).elim
  have heD : (fun ω => extendedCanonicalMass D.process D.rational.terminal
      ((t:WithTop ℝ≥0):ℝ≥0∞) ω) = D.process t := by
    funext ω
    unfold extendedCanonicalMass
    split_ifs with ht
    · congr 1
    · exact (ht hfinite).elim
  rw [heC] at hc
  rw [heD] at hd
  rw [hc,hd]
  ac_rfl

lemma uniqueness_test_terminal_mean (D : CanonicalMass P κ B hBm γ G)
    (f : C_c(upperHalfPlane,ℝ)) (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable) t] E) :
    (∫ ω in E, (∫ z, f z ∂C.process t ω)-(∫ z, f z ∂D.process t ω) ∂P) =
      ∫ ω in E, (∫ z, f z ∂C.rational.terminal ω)-(∫ z, f z ∂D.rational.terminal ω) ∂P := by
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  let (ω : Ω) : (C.rational.terminal ω).Regular := (C.rational.terminal_radon ω).1
  let (ω : Ω) : (D.rational.terminal ω).Regular := (D.rational.terminal_radon ω).1
  let (ω : Ω) : (C.process t ω).Regular := (C.radon t ω).1
  let (ω : Ω) : (D.process t ω).Regular := (D.radon t ω).1
  have hiC := f.integrable.mono_measure (C.uniqueness_process_mean_le t E)
  have hiD := f.integrable.mono_measure (D.uniqueness_process_mean_le t E)
  have hiCT := f.integrable.mono_measure (C.uniqueness_terminal_mean_le E)
  have hiDT := f.integrable.mono_measure (D.uniqueness_terminal_mean_le E)
  have hcross := congrArg (fun μ : Measure upperHalfPlane => ∫ z, f z ∂μ)
    (C.uniqueness_cross_mean D t E hE)
  rw [integral_add_measure hiCT hiD,integral_add_measure hiDT hiC] at hcross
  have heC := integral_bind_of_integrable_sections (P.restrict E) (C.process t)
    (C.progressive.adapted.measurable (i := t)) f f.continuous.measurable (fun _ => f.integrable) hiC
  have heD := integral_bind_of_integrable_sections (P.restrict E) (D.process t)
    (D.progressive.adapted.measurable (i := t)) f f.continuous.measurable (fun _ => f.integrable) hiD
  have heCT := integral_bind_of_integrable_sections (P.restrict E) C.rational.terminal
    C.rational.terminal_measurable f f.continuous.measurable (fun _ => f.integrable) hiCT
  have heDT := integral_bind_of_integrable_sections (P.restrict E) D.rational.terminal
    D.rational.terminal_measurable f f.continuous.measurable (fun _ => f.integrable) hiDT
  rw [integral_sub (C.uniqueness_test_integrable t f).integrableOn
    (D.uniqueness_test_integrable t f).integrableOn,
    integral_sub (C.uniqueness_terminal_test_integrable f).integrableOn
      (D.uniqueness_terminal_test_integrable f).integrableOn,heC,heD,heCT,heDT]
  linarith

variable [IsFiniteMeasure P]

/-- Two canonical mass constructions for the same trace have identical finite
time measures on one full-measure event. -/
theorem process_indistinguishable (D : CanonicalMass P κ B hBm γ G) :
    ∀ᵐ ω ∂P, ∀ t, C.process t ω = D.process t ω := by
  apply random_radon_process_eq_of_positive_tests P (localTestFamily upperHalfPlane)
    C.process D.process (fun t ω => (C.radon t ω).1) (fun t ω => (D.radon t ω).1)
  intro f hf
  apply increasing_mass_unique_of_terminal_mean
    (fun t ω => ∫ z, f z ∂C.process t ω) (fun t ω => ∫ z, f z ∂D.process t ω)
    (fun ω => (∫ z, f z ∂C.rational.terminal ω)-(∫ z, f z ∂D.rational.terminal ω))
    ((C.uniqueness_terminal_test_integrable f).sub (D.uniqueness_terminal_test_integrable f))
    (C.uniqueness_test_adapted f) (D.uniqueness_test_adapted f)
    (fun t => C.uniqueness_test_integrable t f) (fun t => D.uniqueness_test_integrable t f)
    (C.uniqueness_test_terminal_mean D f)
  · filter_upwards [C.paths] with ω hω
    intro s t hst
    let : (C.process t ω).Regular := (C.radon t ω).1
    exact integral_mono_measure (hω.monotone hst) (ae_of_all _ hf) f.integrable
  · filter_upwards [D.paths] with ω hω
    intro s t hst
    let : (D.process t ω).Regular := (D.radon t ω).1
    exact integral_mono_measure (hω.monotone hst) (ae_of_all _ hf) f.integrable
  · filter_upwards [C.paths] with ω hω
    simp only [hω.zero,integral_zero_measure,Pi.zero_apply]
  · filter_upwards [D.paths] with ω hω
    simp only [hω.zero,integral_zero_measure,Pi.zero_apply]
  · filter_upwards [C.paths,D.paths] with ω hc hd
    exact (hc.continuous_tests f).sub (hd.continuous_tests f)

/-- The locally exhausted terminal measures also agree. -/
theorem terminal_ae_eq (D : CanonicalMass P κ B hBm γ G) :
    C.rational.terminal =ᵐ[P] D.rational.terminal := by
  filter_upwards [C.process_indistinguishable D,C.paths,D.paths,C.exhaustion,D.exhaustion]
    with ω he hc hd hlc hld
  let := (C.rational.terminal_radon ω).1
  let := (D.rational.terminal_radon ω).1
  exact radon_terminal_eq_of_common_exhaustion (C.rational.terminal ω) (D.rational.terminal ω)
    (fun t => C.process t ω) hc.dominated (fun t => by rw [he t]; exact hd.dominated t)
    hlc (by simpa only [he] using hld)

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
