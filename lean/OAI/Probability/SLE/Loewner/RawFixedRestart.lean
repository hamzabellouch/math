import OAI.Probability.SLE.Mass.PositiveMassContinuity
import OAI.Probability.SLE.Mass.CanonicalMassRestart
import OAI.Probability.SLE.Mass.RawScaledMassPaths

namespace OAI

/-! Any fixed raw realization with the full-law path certificate restarts
through the actual inverse map. This keeps the raw functional used by scaling. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge.Multipoint
local instance rawFixedRestartMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawFixedRestartBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma CanonicalMass.raw_fixed_restart
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E)
    (hEp : ∀ p∈E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ t, C.process (τ ω+t) ω-C.process (τ ω) ω =
      stoppedFreshMass B κ γ G F hw τ hc R t ω := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hFresh := fresh_capacity_witness_exists hB hm hc hpublished τ hτ
  have hfin := C.stoppedFreshTerminalMass_ae_finite_on_compacts hB hc hκ F hw τ hτ R
    (he.mono fun _ h => h.2) hpublished
  have hraw := sourceRestart_mem_full_driver_set hB hm hc τ hτ E hE hEf
  have hp := stoppedFreshMass_paths B κ γ G F hw τ hc R hm hτ hκ
    (hraw.mono fun _ h => by
      have hr := hEp _ h
      exact ⟨hr.zero,hr.monotone,hr.continuous_real_tests,hr.dominated⟩) hfin
  exact C.stoppedFreshMass_indistinguishable hB hc hκ F hw R he τ hτ hFresh hp

end SLEExactGauge.Multipoint

end

end OAI
