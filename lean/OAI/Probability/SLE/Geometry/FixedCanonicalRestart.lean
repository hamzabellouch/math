import OAI.Probability.SLE.Geometry.NormalizedCanonicalRestart

namespace OAI

/-! Normalized restarting with a single fixed canonical trace factor.
The factor and hence its dense-experiment constants are chosen before the
stopping time and the stopped-past normalization scale. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance fixedCanonicalDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance fixedCanonicalDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance fixedCanonicalPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance fixedCanonicalPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem source_normalized_restart_with_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ)) (hΦ : Measurable Φ)
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hW : ∀ᵐ p ∂P.map (sourceDriverPath B hc),
      IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p))
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (a : Ω → ℝ≥0) (ham : Measurable[hτ.measurableSpace] a) (ha : ∀ ω, 0 < a ω) :
    ∃ Fb : Ω → C(closedHalfPlane, ℂ),
      Measurable[hτ.measurableSpace] Fb ∧
      Measurable (normalizedRestartDriverPath B hc τ a) ∧
      (∀ᵐ ω ∂P, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
      (∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane →
        Fb ω z = F ω (τ ω) ((a ω : ℂ) * z + (Real.sqrt κ * B (τ ω) ω : ℝ))) ∧
      (∀ ω, Fb ω ⟨0, by simp [closedHalfPlane]⟩ = γ ω (τ ω)) ∧
      (∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
        (P.restrict A).map (normalizedRestartDriverPath B hc τ a) =
          P A • P.map (sourceDriverPath B hc)) ∧
      ∀ᵐ ω ∂P,
        IsCapacityTwoWitness
          (normalizedRestartDriver (fun t => Real.sqrt κ * B t ω) (τ ω) (a ω))
          (Φ (normalizedRestartDriverPath B hc τ a ω))
          (Gc (normalizedRestartDriverPath B hc τ a ω))
          (Fc (normalizedRestartDriverPath B hc τ a ω)) ∧
        ∀ t : ℝ≥0, γ ω (τ ω + (a ω) ^ 2 * t) =
          finiteBoundaryPath (Fb ω) (Φ (normalizedRestartDriverPath B hc τ a ω)) t := by
  have hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ
      (fun t p => p t) := by
    refine ⟨fun p t => Φ p t, fun t => (continuous_eval_const t).measurable.comp hΦ, ?_⟩
    filter_upwards [hW] with p hp
    exact ⟨Gc p, Fc p, hp⟩
  obtain ⟨Ψ, GΨ, FΨ, Fb, hΨ, hFb, hYm, hΨorig, hΨW, hFbEq, hFb0, hYlaw, hΨrestart⟩ :=
    source_normalized_canonical_witness_boundary_restart κ hκ hκ8 B hB hm hc γ G F hw
      hpublished hboundary τ hτ a ham ha
  let bp := sourceDriverPath B hc
  let Y := normalizedRestartDriverPath B hc τ a
  have hbp : Measurable bp := source_path_measurable bp hm
  have heq : ∀ᵐ p ∂P.map bp, Φ p = Ψ p := by
    filter_upwards [hW, hΨW] with p hp hΨp
    ext t
    exact congrFun (hp.trace_unique hΨp) t
  have heqBp : ∀ᵐ ω ∂P, Φ (bp ω) = Ψ (bp ω) :=
    ae_of_ae_map (p := fun p => Φ p = Ψ p) hbp.aemeasurable heq
  have hYlaw₀ : P.map Y = P.map bp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using
      hYlaw univ MeasurableSet.univ
  have heqY : ∀ᵐ ω ∂P, Φ (Y ω) = Ψ (Y ω) := by
    apply ae_of_ae_map (p := fun p => Φ p = Ψ p) hYm.aemeasurable
    rwa [hYlaw₀]
  have hYw := canonical_witness_pullback hW Y hYm hYlaw₀
  refine ⟨Fb, hFb, hYm, ?_, hFbEq, hFb0, hYlaw, ?_⟩
  · filter_upwards [heqBp, hΨorig] with ω hω hΨω
    exact hω.trans hΨω
  · filter_upwards [hYw, heqY, hΨrestart] with ω hω heω hrestart
    refine ⟨?_, ?_⟩
    · rw [← normalizedRestartDriverPath_driver κ B hc τ a ω]
      exact hω
    · intro t
      rw [heω]
      exact hrestart.2 t

end SLEExactGauge

end

end OAI
