import OAI.Probability.SLE.Mass.CanonicalMassExtendedRestart
import OAI.Probability.SLE.Geometry.ConformalRestartTransport

namespace OAI

/-! The same raw functional and the same restart event work in every fixed
conformal image. No image-dependent extraction or exceptional set is needed. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance imageRestartDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance imageRestartDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

/-- Every fixed conformal image inherits the pathwise restart identity,
with the same raw functional and one event for all image maps and later times. -/
theorem CanonicalMass.exists_raw_all_image_restart
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t)) :
    ∃ R : RawCanonicalMass,
      (∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
        R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω) ∧
      ∀ (S : Ω → WithTop ℝ≥0)
        (_hS : IsStoppingTime (Filtration.natural B (fun s =>
          (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S),
        ∀ᵐ ω ∂P, S ω < ⊤ → ∀ (D : Set ℂ) (J : upperHalfPlane ≃ₜ D)
          (w : C(upperHalfPlane,ℝ≥0)) (u : ℝ≥0∞),
          conformalMass J w (C.atTime ((((S ω).untopD (0:ℝ≥0):ℝ≥0):ℝ≥0∞)+u) ω)-
              conformalMass J w (C.process ((S ω).untopD (0:ℝ≥0)) ω) =
            conformalMass J w (weightedImageMass
              (stoppedMassPoint B κ γ G F hw (fun ω => (S ω).untopD (0:ℝ≥0)) ω)
              (stoppedMassWeight B κ F (fun ω => (S ω).untopD (0:ℝ≥0)) ω)
              (extendedCanonicalMass R.process R.terminal u
                (sourceRestartDriverPath B hc (fun ω => (S ω).untopD (0:ℝ≥0)) ω))) := by
  obtain ⟨R,he,hr⟩ := C.exists_raw_all_stopping_restart hB hc hκ F hw hpublished
  refine ⟨R,he,?_⟩
  intro S hS
  filter_upwards [hr S hS,C.paths] with ω hω hp
  intro hf D J w u
  let T := (S ω).untopD (0:ℝ≥0)
  have hle : C.process T ω ≤ C.atTime ((T:ℝ≥0∞)+u) ω := by
    by_cases hu : u=∞
    · subst u
      simpa only [CanonicalMass.atTime,add_top,extendedCanonicalMass,lt_self_iff_false,ite_false]
        using hp.dominated T
    · lift u to ℝ≥0 using hu with t
      simpa only [CanonicalMass.atTime,← ENNReal.coe_add,extendedCanonicalMass,
        ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe] using
          hp.monotone (le_add_of_nonneg_right (show 0 ≤ t from zero_le))
  let := (C.atTime_radon ((T:ℝ≥0∞)+u) ω).2
  rw [← conformalMass_sub J w hle]
  exact congrArg (conformalMass J w) (hω hf u)

end SLEExactGauge.Multipoint

end

end OAI
