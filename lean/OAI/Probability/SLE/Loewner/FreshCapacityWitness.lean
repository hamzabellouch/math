import OAI.Probability.SLE.Geometry.CanonicalRestartWitness

namespace OAI

/-! The published trace-generation input is used only on the single
continuous Brownian path law. Strong Markov supplies the fresh witness. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

local instance : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem fresh_capacity_witness_exists
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∃ (β : ℝ≥0 → ℂ) (G' F' : ℝ≥0 → ℂ → ℂ),
      IsCapacityTwoWitness (fun t => Real.sqrt κ*B (τ ω+t) ω-Real.sqrt κ*B (τ ω) ω)
        β G' F' := by
  obtain ⟨Φ,Gc,Fc,_,hW⟩ := exists_measurable_canonical_witness _ κ hpublished
  have hY : Measurable (sourceRestartDriverPath B hc τ) := source_path_measurable _
    (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
  have hLaw : P.map (sourceRestartDriverPath B hc τ)=P.map (sourceDriverPath B hc) := by
    simpa only [Measure.restrict_univ,measure_univ,one_smul] using
      source_restart_continuous_driver_law hB hm hc τ hτ (A := univ) MeasurableSet.univ
  filter_upwards [canonical_witness_pullback hW _ hY hLaw] with ω hω
  refine ⟨Φ (sourceRestartDriverPath B hc τ ω),Gc (sourceRestartDriverPath B hc τ ω),
    Fc (sourceRestartDriverPath B hc τ ω),?_⟩
  convert hω using 1
  funext t
  change Real.sqrt κ*B (τ ω+t) ω-Real.sqrt κ*B (τ ω) ω =
    Real.sqrt κ*(B (τ ω+t) ω-B (τ ω) ω)
  ring

end SLEExactGauge

end

end OAI
