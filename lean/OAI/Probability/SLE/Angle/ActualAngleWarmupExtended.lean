import OAI.Probability.SLE.Geometry.ExtendedMarkedAngle
import OAI.Probability.SLE.Geometry.FiniteCenteredConsistency
import OAI.Probability.SLE.Geometry.ConditionalStopExtension
import OAI.Probability.SLE.Loewner.ActualApproachAtRadius

namespace OAI

/-! The one-unit angular warmup at a literal, possibly infinite, radius
stop. Exact consistency transfers the bound to every later finite centered
law used by the cover experiment. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance extendedWarmupDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance extendedWarmupDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance extendedWarmupPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance extendedWarmupPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem actual_radius_angle_warmup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hW : ∀ᵐ p ∂P.map (sourceDriverPath B hc), IsCapacityTwoWitness
      (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p)) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ (z : ℂ) (hz : z ∈ upperHalfPlane)
      (u : ℝ) (hu : 0 ≤ u) (V : ℝ), u + 1 ≤ V →
      ∀ A : Set Ω, MeasurableSet[(actual_radiusLevelTime_stopping hB
        (fun _t => hBm.comp (measurable_const.prodMk measurable_id)) hBm hc hB0
        κ hκ hκ8 γ G F hw z hz u hu).measurableSpace] A →
        ENNReal.ofReal (1 / 2 : ℝ) * finiteCenteredLaw P κ B γ G z V A ≤
          finiteCenteredLaw P κ B γ G z V
            (A ∩ {ω | canonicalRadiusLevel κ (u + 1, z, sourceDriverPath B hc ω) < ∞ ∧
              s ≤ canonicalStoppedSine κ (u + 1, z, sourceDriverPath B hc ω)}) := by
  classical
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨s₀, hs₀, hstep⟩ := actual_one_unit_angle_warmup P κ hκ hκ8 B hB hBm hc hB0
    γ G F hw Φ Gc Fc hW
  let s := min s₀ 1
  have hs : 0 < s := lt_min hs₀ zero_lt_one
  have hss₀ : s ≤ s₀ := min_le_left _ _
  refine ⟨s, hs, min_le_right _ _, ?_⟩
  intro z hz u hu V hV A hA
  let σ : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  have hσ := actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz u hu
  let Q := finiteCenteredLaw P κ B γ G z (u + 1)
  let S : Set Ω := {ω | canonicalRadiusLevel κ (u + 1, z, sourceDriverPath B hc ω) < ∞ ∧
    s ≤ canonicalStoppedSine κ (u + 1, z, sourceDriverPath B hc ω)}
  let E := A ∩ {ω | σ ω ≠ ⊤}
  have hE : MeasurableSet[hσ.measurableSpace] E :=
    hA.inter ((measurableSet_singleton (⊤ : WithTop ℝ≥0)).preimage hσ.measurable).compl
  have hfinite : ∀ᵐ ω ∂Q, σ ω ≠ ⊤ :=
    finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F (Eventually.of_forall hw)
      z hz u (u + 1) hu (by linarith) σ (Eventually.of_forall fun _ => le_rfl)
  have hEeq : E =ᵐ[Q] A := by
    filter_upwards [hfinite] with ω hω
    exact propext (and_iff_left hω)
  let state : Ω → ℝ≥0 → Prop := fun ω t =>
    z ∈ survivingDomain (γ ω) t ∧ fullRadius (G ω) t z = (2 * z.im) * Real.exp (-u)
  have hlocal : ∀ (τ : Ω → ℝ≥0)
      (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0)))
      (D : Set Ω), MeasurableSet[hτ.measurableSpace] D →
      (∀ ω ∈ D, state ω (τ ω)) → ENNReal.ofReal (1 / 2 : ℝ) * Q D ≤ Q (D ∩ S) := by
    intro τ hτ D hD hstate
    have h := hstep τ hτ z hz u hu D hD (fun ω hω => (hstate ω hω).1)
      (fun ω hω => (hstate ω hω).2) D hD
    simp only [inter_self] at h
    apply h.trans (measure_mono ?_)
    intro ω hω
    exact ⟨hω.1, hω.2.1, hss₀.trans hω.2.2⟩
  have hstate : ∀ ω ∈ E, state ω ((σ ω).untopD 0) := by
    intro ω hω
    exact actual_radius_level_finite_state (hw ω) ((hc ω).const_mul _) z u hω.2
  have hext := conditional_event_bound_at_extended_stop Q _ (ENNReal.ofReal (1 / 2 : ℝ))
    S state hlocal σ hσ E hE (hfinite.mono fun _ h _ => h) hstate
  have hbase : ENNReal.ofReal (1 / 2 : ℝ) * Q A ≤ Q (A ∩ S) := by
    rw [measure_congr hEeq] at hext
    have hES : E ∩ S =ᵐ[Q] A ∩ S := by
      filter_upwards [hEeq] with ω hω
      exact propext (and_congr_left fun _ => Iff.of_eq hω)
    rwa [measure_congr hES] at hext
  have hσ₁ := actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz
    (u + 1) (by linarith)
  have hA₁ : MeasurableSet[hσ₁.measurableSpace] A :=
    actual_radiusLevelTime_past_mono hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz u (u + 1)
      hu (by linarith) A hA
  have hS₁ : MeasurableSet[hσ₁.measurableSpace] S :=
    canonical_good_angle_measurable_at_radius hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz
      (u + 1) s (by linarith)
  have hcons (D : Set Ω) (hD : MeasurableSet[hσ₁.measurableSpace] D) :
      finiteCenteredLaw P κ B γ G z V D = Q D :=
    finiteCenteredLaw_consistent_at_radius_stop hB hBm hc hB0 κ hκ hκ8 γ G F
      (Eventually.of_forall hw) z hz (u + 1) V (by linarith) hV _ hσ₁
      (Eventually.of_forall fun _ => rfl) D hD
  rw [hcons A hA₁, hcons (A ∩ S) (hA₁.inter hS₁)]
  exact hbase

end SLEExactGauge

end

end OAI
