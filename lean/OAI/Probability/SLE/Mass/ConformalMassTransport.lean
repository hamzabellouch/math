import OAI.Probability.SLE.Mass.CanonicalMassAllVisits
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! The weighted pushforward used for canonical mass in a conformal
image. Compact tests pull back with the same deterministic convex sequence;
the construction does not extract a new subsequence for the image domain. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

variable {D : Set ℂ}

/-- For a conformal identification, `w` is the continuous weight `|J'|^d`. -/
def conformalMass (J : upperHalfPlane ≃ₜ D) (w : C(upperHalfPlane, ℝ≥0))
    (μ : Measure upperHalfPlane) : Measure D :=
  (μ.withDensity (fun z => (w z : ℝ≥0∞))).map J

def conformalMassTest (J : upperHalfPlane ≃ₜ D) (w : C(upperHalfPlane, ℝ≥0))
    (f : C_c(D, ℝ)) : C_c(upperHalfPlane, ℝ) :=
  (⟨fun z => (w z : ℝ), continuous_subtype_val.comp w.continuous⟩ :
    C(upperHalfPlane, ℝ)) • f.comp J.toCocompactMap

@[simp] lemma conformalMassTest_apply (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) (f : C_c(D, ℝ)) (z : upperHalfPlane) :
    conformalMassTest J w f z = (w z : ℝ) * f (J z) := rfl

lemma conformalMass_integral (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) (μ : Measure upperHalfPlane) (f : C_c(D, ℝ)) :
    (∫ z, f z ∂conformalMass J w μ) = ∫ z, conformalMassTest J w f z ∂μ := by
  rw [conformalMass,integral_map_of_stronglyMeasurable J.continuous.measurable
    (show StronglyMeasurable (fun z => f z) from f.continuous.stronglyMeasurable),
    integral_withDensity_eq_integral_smul w.continuous.measurable]
  rfl

lemma conformalMass_radon (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) (μ : Measure upperHalfPlane)
    [IsFiniteMeasureOnCompacts μ] :
    (conformalMass J w μ).Regular ∧ IsFiniteMeasureOnCompacts (conformalMass J w μ) := by
  let : IsLocallyFiniteMeasure (μ.withDensity (fun z => (w z : ℝ≥0∞))) :=
    IsLocallyFiniteMeasure.withDensity_coe w.continuous
  have : (μ.withDensity (fun z => (w z : ℝ≥0∞))).Regular := inferInstance
  exact ⟨Measure.Regular.map J,Measure.IsFiniteMeasureOnCompacts.map _ J⟩

lemma conformalMass_measurable (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) : Measurable (conformalMass J w) := by
  apply (Measure.measurable_map J J.continuous.measurable).comp
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [withDensity_apply _ hA]
  simp_rw [← lintegral_indicator hA]
  exact Measure.measurable_lintegral
    ((w.continuous.measurable.coe_nnreal_ennreal).indicator hA)

@[simp] lemma conformalMass_zero (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) : conformalMass J w 0 = 0 := by
  simp [conformalMass]

lemma conformalMass_add (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) (μ ν : Measure upperHalfPlane) :
    conformalMass J w (μ+ν) = conformalMass J w μ + conformalMass J w ν := by
  simp only [conformalMass,withDensity_add_measure]
  exact Measure.map_add _ _ J.continuous.measurable

lemma conformalMass_mono (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) {μ ν : Measure upperHalfPlane} (h : μ ≤ ν) :
    conformalMass J w μ ≤ conformalMass J w ν := by
  apply Measure.map_mono ?_ J.continuous.measurable
  apply Measure.le_iff.mpr
  intro A hA
  simp only [withDensity_apply _ hA]
  exact lintegral_mono' (Measure.restrict_mono le_rfl h) le_rfl

lemma conformalMass_nullSingleton (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) (μ : Measure upperHalfPlane) [NullSingletonClass μ] :
    NullSingletonClass (conformalMass J w μ) := by
  constructor
  intro z
  rw [conformalMass,Measure.map_apply J.continuous.measurable (measurableSet_singleton z)]
  rw [show J ⁻¹' {z} = {J.symm z} by
    ext x
    simp only [mem_preimage,mem_singleton_iff]
    constructor
    · intro h
      exact J.injective (h.trans (J.apply_symm_apply z).symm)
    · intro h
      rw [h,J.apply_symm_apply]]
  exact measure_singleton _

lemma conformalMass_carried (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) (μ : Measure upperHalfPlane)
    (S : Set upperHalfPlane) (hS : MeasurableSet S) (hμ : μ Sᶜ = 0) :
    conformalMass J w μ (J '' S)ᶜ = 0 := by
  rw [conformalMass,Measure.map_apply J.continuous.measurable
    (J.measurableEmbedding.measurableSet_image.mpr hS).compl]
  apply withDensity_absolutelyContinuous μ _
  simpa only [preimage_compl,Set.preimage_image_eq _ J.injective] using hμ

/-- Vague convergence transfers for every image-domain test on the same
event and with the same sequence. -/
lemma conformalMass_test_tendsto (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) (μ : ℕ → Measure upperHalfPlane)
    (ν : Measure upperHalfPlane)
    (h : ∀ f : C_c(upperHalfPlane, ℝ),
      Tendsto (fun n => ∫ z, f z ∂μ n) atTop (𝓝 (∫ z, f z ∂ν)))
    (f : C_c(D, ℝ)) :
    Tendsto (fun n => ∫ z, f z ∂conformalMass J w (μ n)) atTop
      (𝓝 (∫ z, f z ∂conformalMass J w ν)) := by
  simp only [conformalMass_integral]
  exact h (conformalMassTest J w f)

lemma conformalMass_test_continuous (J : upperHalfPlane ≃ₜ D)
    (w : C(upperHalfPlane, ℝ≥0)) (μ : ℝ≥0 → Measure upperHalfPlane)
    (h : ∀ f : C_c(upperHalfPlane, ℝ), Continuous (fun t => ∫ z, f z ∂μ t))
    (f : C_c(D, ℝ)) : Continuous (fun t => ∫ z, f z ∂conformalMass J w (μ t)) := by
  simp only [conformalMass_integral]
  exact h (conformalMassTest J w f)

end SLEExactGauge.Multipoint

end

end OAI
