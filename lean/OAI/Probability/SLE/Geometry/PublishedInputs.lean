import OAI.Probability.SLE.Gauge.LargerGaugeMain

namespace OAI

/-!
Precisely specialized published input for a Brownian-driven presentation.

S. Rohde and O. Schramm, *Basic properties of SLE*, Annals of Mathematics
161 (2005), 883–924, Theorem 5.1 (Continuity), p. 899;
https://annals.math.princeton.edu/wp-content/uploads/annals-v161-n2-p07.pdf.

Only existence of a measurable continuous capacity-two trace is requested.
The Loewner equations and inverse-tip limit in `IsCapacityTwoTrace` fix its
normalization. No Hausdorff bound is included in this input. It is a parameter
of the conditional theorem below, not a global axiom.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- The consequence of Rohde–Schramm Theorem 5.1 needed to pass from a
Brownian driver to the continuous trace convention used in this development. -/
def PublishedTraceGeneration
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ γ : Ω → ℝ≥0 → ℂ,
    (∀ t, Measurable (fun ω => γ ω t)) ∧
    ∀ᵐ ω ∂P, IsCapacityTwoTrace (fun t => Real.sqrt κ * B t ω) (γ ω)

/-- The actual larger-gauge main corollary, conditional only on the published
trace-generation input when starting from a Brownian driver. -/
theorem larger_gauge_corollary_of_published_trace_generation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P)
    (hpublished : PublishedTraceGeneration P κ B) :
    ∃ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P ∧
      ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
        (¬ SigmaFinite ((hausdorffGauge (schrammGauge κ)).restrict
          (segment (γ ω) s t))) ∧
        hausdorffGauge (schrammGauge κ) (segment (γ ω) s t) = ∞ := by
  obtain ⟨γ, hm, htrace⟩ := hpublished
  have hSLE : IsOrdinaryChordalSLE κ γ P := ⟨hm, B, hB, htrace⟩
  refine ⟨γ, hSLE, ?_⟩
  filter_upwards [schramm_gauge_not_sigmaFinite_on_all_segments P κ hκ hκ8 γ hSLE,
    schramm_gauge_infinite_on_all_segments P κ hκ hκ8 γ hSLE]
    with ω hσ hinfinite s t hs hst
  exact ⟨hσ s t hs hst, hinfinite s t hs hst⟩

end SLEExactGauge

end

end OAI
