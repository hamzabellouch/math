import OAI.Probability.SLE.Gauge.GaugeGrowthDischarge
import OAI.Probability.SLE.Mass.CanonicalMassImageRestart

namespace OAI

/-! Finite and terminal stopping-time restart identities using a capacity
trace witness for the canonical driver law. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance restartDischargeDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance restartDischargeDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

theorem CanonicalMass.exists_raw_all_stopping_restart_of_brownian_witness
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hκ8 : κ < 8) (hB0 : ∀ ω, B 0 ω = 0) :
    ∃ R : RawCanonicalMass,
      (∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
        R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω) ∧
      ∀ (S : Ω → WithTop ℝ≥0)
        (_hS : IsStoppingTime (Filtration.natural B (fun s =>
          (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S),
        ∀ᵐ ω ∂P, S ω < ⊤ → ∀ u : ℝ≥0∞,
          extendedCanonicalMass C.process C.rational.terminal
              ((((S ω).untopD (0 : ℝ≥0) : ℝ≥0) : ℝ≥0∞)+u) ω-C.process ((S ω).untopD (0 : ℝ≥0)) ω =
            weightedImageMass
              (stoppedMassPoint B κ γ G F hw (fun ω => (S ω).untopD (0 : ℝ≥0)) ω)
              (stoppedMassWeight B κ F (fun ω => (S ω).untopD (0 : ℝ≥0)) ω)
              (extendedCanonicalMass R.process R.terminal u
                (sourceRestartDriverPath B hc (fun ω => (S ω).untopD (0 : ℝ≥0)) ω)) := by
  exact C.exists_raw_all_stopping_restart hB hc hκ F hw
    (canonical_driver_trace_generation_of_witness κ hκ hκ8 B hB
      (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hc hB0 γ G F hw)

theorem CanonicalMass.exists_raw_all_image_restart_of_brownian_witness
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hκ8 : κ < 8) (hB0 : ∀ ω, B 0 ω = 0) :
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
  exact C.exists_raw_all_image_restart hB hc hκ F hw
    (canonical_driver_trace_generation_of_witness κ hκ hκ8 B hB
      (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hc hB0 γ G F hw)

end SLEExactGauge.Multipoint

end

end OAI
