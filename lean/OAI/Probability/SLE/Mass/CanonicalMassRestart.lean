import OAI.Probability.SLE.Loewner.StoppedInverseTerminalUniqueness

namespace OAI

/-! The canonical raw driver functional restarts through the actual inverse
Loewner chart. The trace-generation input is precisely the published one
already used for ordinary SLE, and strong Markov provides each fresh path. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance canonicalRestartDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance canonicalRestartDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

/-- One raw functional realizes the original mass and satisfies the finite
and terminal pathwise restart identities at every finite stopping time. -/
theorem CanonicalMass.exists_raw_pathwise_restart
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t)) :
    ∃ R : RawCanonicalMass,
      (∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
        R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω) ∧
      ∀ (τ : Ω → ℝ≥0)
        (_hτ : IsStoppingTime (Filtration.natural B (fun s =>
          (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
          (fun ω => (τ ω:WithTop ℝ≥0))),
        ∀ᵐ ω ∂P,
          (∀ t : ℝ≥0, C.process (τ ω+t) ω-C.process (τ ω) ω =
            stoppedFreshMass B κ γ G F hw τ hc R t ω) ∧
          C.rational.terminal ω-C.process (τ ω) ω =
            stoppedFreshTerminalMass B κ γ G F hw τ hc R ω := by
  obtain ⟨R,he,hr⟩ := C.exists_raw_restarted_canonical hB hc
  refine ⟨R,he,?_⟩
  intro τ hτ
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hFresh := fresh_capacity_witness_exists hB hm hc hpublished τ hτ
  have hfin := C.stoppedFreshTerminalMass_ae_finite_on_compacts hB hc hκ F hw τ hτ R
    (he.mono fun _ h => h.2) hpublished
  have hraw := (hr τ hτ).2
  have hp := stoppedFreshMass_paths B κ γ G F hw τ hc R hm hτ hκ
    (hraw.mono fun _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩) hfin
  have hx := stoppedFreshMass_terminal_exhaustion B κ γ G F hw τ hc R hm hτ hκ
    (hraw.mono fun _ h => h.2.2.2.1) (hraw.mono fun _ h => h.2.2.2.2) hfin
  filter_upwards [C.stoppedFreshMass_indistinguishable hB hc hκ F hw R he τ hτ hFresh hp,
    C.stoppedFreshTerminalMass_eq_remainder hB hc hκ F hw R he τ hτ hFresh hp hfin hx]
    with ω hf ht
  exact ⟨hf,ht⟩

end SLEExactGauge.Multipoint

end

end OAI
