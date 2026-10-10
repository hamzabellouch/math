import OAI.Probability.SLE.Mass.ConformalMassTransport

namespace OAI

/-! The canonical process in a fixed conformal image. The pathwise limit
event is common to all image maps and compact tests. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) {D : Set ℂ}

def imageProcess (J : upperHalfPlane ≃ₜ D) (w : C(upperHalfPlane,ℝ≥0))
    (t : ℝ≥0) (ω : Ω) : Measure D := conformalMass J w (C.process t ω)

lemma imageProcess_progressive (J : upperHalfPlane ≃ₜ D) (w : C(upperHalfPlane,ℝ≥0)) :
    IsProgressive (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable))
      (C.imageProcess J w) := by
  intro t
  exact (conformalMass_measurable J w).comp (C.progressive t)

lemma imageProcess_radon (J : upperHalfPlane ≃ₜ D) (w : C(upperHalfPlane,ℝ≥0))
    (t : ℝ≥0) (ω : Ω) :
    (C.imageProcess J w t ω).Regular ∧ IsFiniteMeasureOnCompacts (C.imageProcess J w t ω) := by
  let := (C.radon t ω).2
  exact conformalMass_radon J w (C.process t ω)

lemma imageProcess_paths (J : upperHalfPlane ≃ₜ D) (w : C(upperHalfPlane,ℝ≥0)) :
    ∀ᵐ ω ∂P, C.imageProcess J w 0 ω = 0 ∧
      Monotone (fun t => C.imageProcess J w t ω) ∧
      (∀ t, C.imageProcess J w t ω ≤ conformalMass J w (C.rational.terminal ω)) ∧
      (∀ f : C_c(D,ℝ), Continuous (fun t => ∫ z, f z ∂C.imageProcess J w t ω)) ∧
      NullSingletonClass (conformalMass J w (C.rational.terminal ω)) := by
  filter_upwards [C.paths,C.rational.nonatomic] with ω hp hn
  let := hn
  refine ⟨?_,?_,?_,?_,conformalMass_nullSingleton J w _⟩
  · simp only [imageProcess,hp.zero,conformalMass_zero]
  · intro s t hst
    exact conformalMass_mono J w (hp.monotone hst)
  · intro t
    exact conformalMass_mono J w (hp.dominated t)
  · exact conformalMass_test_continuous J w (fun t => C.process t ω) hp.continuous_tests

/-- No image map changes the extraction: one event works for every map,
every continuous nonnegative weight, all extended times, and all tests. -/
theorem all_image_limits
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ) (hκ8 : κ < 8)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) :
    ∀ᵐ ω ∂P, ∀ (D : Set ℂ) (J : upperHalfPlane ≃ₜ D)
      (w : C(upperHalfPlane,ℝ≥0)) (t : ℝ≥0∞) (f : C_c(D,ℝ)),
      Tendsto (fun n => ∫ z, f z ∂conformalMass J w
        (convexLevelMeasure κ B γ G (fun n => (n:ℝ)) C.rational.supports C.rational.weights n t ω))
        atTop (𝓝 (∫ z, f z ∂conformalMass J w (C.atTime t ω))) := by
  filter_upwards [C.rational.all_extended_times_limit hBc hκ hκ8 F hw
    C.process C.radon C.paths] with ω hω
  intro D J w t f
  exact conformalMass_test_tendsto J w _ _ (hω t) f

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
