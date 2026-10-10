import OAI.Probability.SLE.Gauge.ActualDenseGoodState
import OAI.Probability.SLE.Geometry.ConditionalStopExtension

namespace OAI

/-! The proved dense experiment at possibly infinite actual radius stops.
Only the good-state past event is localized through finite horizons. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

local instance extendedDenseDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance extendedDenseDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance extendedDensePathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance extendedDensePathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem uniform_actual_dense_at_extended_good_radius_state
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hγm : ∀ t, Measurable (fun ω => γ ω t))
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (htrace : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ h b C : ℝ, 0 < h ∧ h ≤ s / 2 ∧ 0 < b ∧ 0 < C ∧
      ∃ δ : ℕ → ℝ, (∀ N, 0 < N → 0 < δ N) ∧
      ∀ (σ : Ω → WithTop ℝ≥0)
        (hσ : IsStoppingTime (Filtration.natural B
          (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable)) σ)
        (z : ℂ), z ∈ upperHalfPlane → ∀ u : ℝ, 0 ≤ u →
        ∀ E : Set Ω, MeasurableSet[hσ.measurableSpace] E →
          (∀ ω ∈ E, σ ω ≠ ⊤) →
          E ⊆ stoppedMarkedGood κ B γ G (fun ω => (σ ω).untopD 0) z s →
          (∀ ω ∈ E, fullRadius (G ω) ((σ ω).untopD 0) z = (2 * z.im) * Real.exp (-u)) →
          ∀ N : ℕ, 0 < N → ∀ v : ℝ, 0 < v →
            v < δ N * ((2 * z.im) * Real.exp (-u)) →
            ∀ A : Set Ω, MeasurableSet[hσ.measurableSpace] A →
              ENNReal.ofReal (Real.exp (-C * (N : ℝ) ^ 2)) *
                finiteCenteredLaw P κ B γ G z (u + Serpentine.experimentRadiusLevel h) (A ∩ E) ≤
              finiteCenteredLaw P κ B γ G z (u + Serpentine.experimentRadiusLevel h)
                (A ∩ E ∩ stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
                  (fun ω => radiusLevelTime (γ ω) (G ω) z (u + Serpentine.experimentRadiusLevel h))
                  (closedBall z ((2 * z.im) * Real.exp (-u)))
                  (b * ((2 * z.im) * Real.exp (-u)) ^ dimension κ * (N : ℝ) ^ codimension κ)) := by
  obtain ⟨h, b, C, hh, hhs, hb, hC, δ, hδ, hstep⟩ :=
    uniform_actual_dense_at_good_radius_state P κ hκ hκ8 B hB hBm hc hB0 γ G F hγm hw
      htrace hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW hs hs1
  refine ⟨h, b, C, hh, hhs, hb, hC, δ, hδ, ?_⟩
  intro σ hσ z hz u hu E hE hfinite hgood hbase N hN v hv hvcut A hA
  let Q := finiteCenteredLaw P κ B γ G z (u + Serpentine.experimentRadiusLevel h)
  let S := stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
    (fun ω => radiusLevelTime (γ ω) (G ω) z (u + Serpentine.experimentRadiusLevel h))
    (closedBall z ((2 * z.im) * Real.exp (-u)))
    (b * ((2 * z.im) * Real.exp (-u)) ^ dimension κ * (N : ℝ) ^ codimension κ)
  let state : Ω → ℝ≥0 → Prop := fun ω t =>
    ω ∈ stoppedMarkedGood κ B γ G (fun _ => t) z s ∧
      fullRadius (G ω) t z = (2 * z.im) * Real.exp (-u)
  apply conditional_event_bound_at_extended_stop Q _
    (ENNReal.ofReal (Real.exp (-C * (N : ℝ) ^ 2))) S state _ σ hσ (A ∩ E) (hA.inter hE)
    (Eventually.of_forall (fun ω hω => hfinite ω hω.2))
  · intro ω hω
    exact ⟨hgood hω.2, hbase ω hω.2⟩
  · intro τ hτ D hD hstate
    have hDgood : D ⊆ stoppedMarkedGood κ B γ G τ z s := fun ω hω => (hstate ω hω).1
    have hDbase : ∀ ω ∈ D, fullRadius (G ω) (τ ω) z = (2 * z.im) * Real.exp (-u) :=
      fun ω hω => (hstate ω hω).2
    simpa only [inter_self] using hstep τ hτ z hz u hu D hD hDgood hDbase N hN v hv hvcut D hD

end SLEExactGauge

end

end OAI
