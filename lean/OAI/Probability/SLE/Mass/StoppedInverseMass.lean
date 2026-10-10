import OAI.Probability.SLE.Geometry.RestartDerivativeMeasurability
import OAI.Probability.SLE.Geometry.CanonicalRawMean
import OAI.Probability.SLE.Mass.WeightedImageRandomMass

namespace OAI

/-! Actual stopped inverse-Loewner transport of the fresh raw terminal
mass, with measurable charts, derivative weights and exact spatial tests. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
local instance : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  (B : ℝ≥0 → Ω → ℝ) (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ)
  (G F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (τ : Ω → ℝ≥0)

def stoppedMassPoint (ω : Ω) (z : upperHalfPlane) : upperHalfPlane :=
  ⟨F ω (τ ω) ((z:ℂ)+(Real.sqrt κ*B (τ ω) ω:ℝ)),
    ((hw ω).2.2.2.2.2.2.1 (τ ω) (by
      simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
        using z.property)).1.1⟩

def stoppedMassWeight (ω : Ω) (z : upperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (‖deriv (F ω (τ ω)) ((z:ℂ)+(Real.sqrt κ*B (τ ω) ω:ℝ))‖^dimension κ)

variable (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
  (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω:WithTop ℝ≥0)))

include hm hc hτ γ G hw

theorem stoppedMassPoint_measurable : Measurable[hτ.measurableSpace.prod inferInstance]
    (fun p : Ω × upperHalfPlane => stoppedMassPoint B κ γ G F hw τ p.1 p.2) := by
  unfold stoppedMassPoint
  apply Measurable.subtype_mk
  exact continuous_eval.measurable.comp
    (((source_stopped_inversePath_measurable B hm hc κ γ G F hw τ hτ).comp
      measurable_fst).prodMk measurable_snd)

theorem stoppedMassWeight_measurable (hκ : 0 < κ) :
    Measurable[hτ.measurableSpace.prod inferInstance]
      (fun p : Ω × upperHalfPlane => stoppedMassWeight B κ F τ p.1 p.2) := by
  let : MeasurableSpace (Ω × upperHalfPlane) := hτ.measurableSpace.prod inferInstance
  have hd := source_stopped_inverse_derivative_measurable B hm hc κ γ G F hw τ hτ
  have he : 0 ≤ dimension κ := by unfold dimension; linarith
  exact ((Real.continuous_rpow_const he).measurable.comp hd.norm).ennreal_ofReal

omit hm hτ in
def stoppedFreshTerminalMass (R : RawCanonicalMass) (ω : Ω) : Measure upperHalfPlane :=
  weightedImageMass (stoppedMassPoint B κ γ G F hw τ ω) (stoppedMassWeight B κ F τ ω)
    (R.terminal (sourceRestartDriverPath B hc τ ω))

theorem stoppedFreshTerminalMass_measurable (hκ : 0 < κ) (R : RawCanonicalMass) :
    Measurable (stoppedFreshTerminalMass B κ γ G F hw τ hc R) := by
  have hY : Measurable (sourceRestartDriverPath B hc τ) := source_path_measurable _
    (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
  have hM := @weightedImageMass_measurable_of_subsigma Ω upperHalfPlane mΩ inferInstance
    hτ.measurableSpace hτ.measurableSpace_le
    (fun ω => R.terminal (sourceRestartDriverPath B hc τ ω))
    (R.terminal_measurable.comp hY) (fun ω => (R.terminal_radon _).2)
    (fun p => stoppedMassPoint B κ γ G F hw τ p.1 p.2)
    (stoppedMassPoint_measurable B κ γ G F hw τ hm hc hτ)
    (fun p => stoppedMassWeight B κ F τ p.1 p.2)
    (stoppedMassWeight_measurable B κ γ G F hw τ hm hc hτ hκ)
  exact hM

theorem CanonicalMass.stoppedFreshTerminalMass_test
    {P : Measure Ω} [IsProbabilityMeasure P] {hBm : Measurable (Function.uncurry B)}
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P) (hκ : 0 < κ)
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, R.terminal (sourceDriverPath B hc ω) = C.rational.terminal ω)
    (f : Ω × upperHalfPlane → ℝ≥0∞)
    (hf : Measurable[hτ.measurableSpace.prod inferInstance] f) :
    (∫⁻ ω, ∫⁻ x, f (ω,x) ∂(stoppedFreshTerminalMass B κ γ G F hw τ hc R ω) ∂P) =
      ∫⁻ ω, ∫⁻ z, stoppedMassWeight B κ F τ ω z *
        f (ω,stoppedMassPoint B κ γ G F hw τ ω z) ∂initialGreenMeasure κ ∂P := by
  have hp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  let : IsProbabilityMeasure (P.map (sourceDriverPath B hc)) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hY : Measurable (sourceRestartDriverPath B hc τ) := source_path_measurable _
    (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
  have h := restart_weighted_mass_test P (P.map (sourceDriverPath B hc))
    hτ.measurableSpace hτ.measurableSpace_le (sourceRestartDriverPath B hc τ) hY
    (fun A hA => source_restart_continuous_driver_law hB hm hc τ hτ hA)
    R.terminal R.terminal_measurable (fun p => (R.terminal_radon p).2) _
    (stoppedMassPoint_measurable B κ γ G F hw τ hm hc hτ) _
    (stoppedMassWeight_measurable B κ γ G F hw τ hm hc hτ hκ) f hf
  rwa [C.raw_terminal_mean hc R he] at h

end SLEExactGauge.Multipoint

end

end OAI
