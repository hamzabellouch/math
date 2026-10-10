import OAI.Probability.SLE.Mass.CanonicalMassRestart
import OAI.Probability.SLE.Geometry.ExtendedStopLocalization

namespace OAI

/-! Pathwise canonical restart at every possibly infinite stopping time,
on its finite event, simultaneously for all finite and terminal later times. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance extendedRestartDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance extendedRestartDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

/-- One raw functional works at every stopping time. The equality is of
whole measures, hence permits random later times and nonnegative Borel tests. -/
theorem CanonicalMass.exists_raw_all_stopping_restart
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
        ∀ᵐ ω ∂P, S ω < ⊤ → ∀ u : ℝ≥0∞,
          extendedCanonicalMass C.process C.rational.terminal
              ((((S ω).untopD (0 : ℝ≥0) : ℝ≥0) : ℝ≥0∞)+u) ω-C.process ((S ω).untopD (0 : ℝ≥0)) ω =
            weightedImageMass
              (stoppedMassPoint B κ γ G F hw (fun ω => (S ω).untopD (0 : ℝ≥0)) ω)
              (stoppedMassWeight B κ F (fun ω => (S ω).untopD (0 : ℝ≥0)) ω)
              (extendedCanonicalMass R.process R.terminal u
                (sourceRestartDriverPath B hc (fun ω => (S ω).untopD (0 : ℝ≥0)) ω)) := by
  obtain ⟨R,he,hr⟩ := C.exists_raw_pathwise_restart hB hc hκ F hw hpublished
  refine ⟨R,he,?_⟩
  intro S hS
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  let Q : Ω → ℝ≥0 → Prop := fun ω T => ∀ u : ℝ≥0∞,
    extendedCanonicalMass C.process C.rational.terminal ((T:ℝ≥0∞)+u) ω-C.process T ω =
      weightedImageMass (stoppedMassPoint B κ γ G F hw (fun _ => T) ω)
        (stoppedMassWeight B κ F (fun _ => T) ω)
        (extendedCanonicalMass R.process R.terminal u
          (sourceRestartDriverPath B hc (fun _ => T) ω))
  have hQ (n : ℕ) : ∀ᵐ ω ∂P, Q ω (cutoffStop S n ω) := by
    have hτ := cutoffStop_stopping ℱ S hS (n:ℝ≥0)
    filter_upwards [hr (cutoffStop S n) hτ] with ω hω
    have hp : stoppedMassPoint B κ γ G F hw (cutoffStop S n) ω =
        stoppedMassPoint B κ γ G F hw (fun _ => cutoffStop S n ω) ω := by
      funext z
      apply Subtype.ext
      rfl
    have hv : stoppedMassWeight B κ F (cutoffStop S n) ω =
        stoppedMassWeight B κ F (fun _ => cutoffStop S n ω) ω := rfl
    have hy : sourceRestartDriverPath B hc (cutoffStop S n) ω =
        sourceRestartDriverPath B hc (fun _ => cutoffStop S n ω) ω := by
      ext t
      rfl
    intro u
    by_cases hu : u=∞
    · subst u
      have ht := hω.2
      unfold stoppedFreshTerminalMass at ht
      rw [hp,hv,hy] at ht
      simpa only [Q,add_top,extendedCanonicalMass,lt_self_iff_false,ite_false] using ht
    · lift u to ℝ≥0 using hu with t
      have ht := hω.1 t
      unfold stoppedFreshMass at ht
      rw [hp,hv,hy] at ht
      simpa only [Q,← ENNReal.coe_add,extendedCanonicalMass,ENNReal.coe_lt_top,
        ite_true,ENNReal.toNNReal_coe] using ht
  filter_upwards [ae_of_cutoffStop S P Q hQ] with ω hω
  intro hf u
  have hp : stoppedMassPoint B κ γ G F hw (fun ω => (S ω).untopD (0:ℝ≥0)) ω =
      stoppedMassPoint B κ γ G F hw (fun _ => (S ω).untopD (0:ℝ≥0)) ω := by
    funext z
    apply Subtype.ext
    rfl
  have hv : stoppedMassWeight B κ F (fun ω => (S ω).untopD (0:ℝ≥0)) ω =
      stoppedMassWeight B κ F (fun _ => (S ω).untopD (0:ℝ≥0)) ω := rfl
  have hy : sourceRestartDriverPath B hc (fun ω => (S ω).untopD (0:ℝ≥0)) ω =
      sourceRestartDriverPath B hc (fun _ => (S ω).untopD (0:ℝ≥0)) ω := by
    ext t
    rfl
  rw [hp,hv,hy]
  exact hω hf u

end SLEExactGauge.Multipoint

end

end OAI
