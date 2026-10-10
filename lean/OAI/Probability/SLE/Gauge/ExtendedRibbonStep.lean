import OAI.Probability.SLE.Gauge.ConditionalRibbonStep
import OAI.Probability.SLE.Gauge.ExtendedExperimentStop

namespace OAI

/-! First-front stops may be infinite on failed experiments. Exhaust the
admissible event through finite horizons, so the actual finite-stop
restart bound applies without requiring completion on failed samples. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates BoundaryScaleLaw Target

local instance extendedRibbonPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance extendedRibbonPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def shiftedActualTrace {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (hc : ∀ ω, Continuous (γ ω)) (ω : Ω) (t : ℝ≥0) : C(ℝ≥0, ℂ) :=
  ⟨fun s => γ ω (t + s), (hc ω).comp (continuous_const.add continuous_id)⟩

def ActualRibbonAdmissible {Ω : Type*} (U : Ω → ℝ≥0 → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (C L : ℝ≥0) (ε κ v c : ℝ) (S : Set C(ℝ≥0, ℂ)) (ω : Ω) (t : ℝ≥0) : Prop :=
  ∃ d : RibbonHistory C L ε, d.U = U ω ∧ d.trace = γ ω ∧
    d.forward = G ω ∧ d.inverse = F ω ∧ d.time = t ∧ d.stepEvent κ v c = S

/-- The quantitative actual ribbon restart bound extends to a stopping
time finite on the admissible past event. All future traces use the
original random completion time, rather than its horizon truncations. -/
theorem actual_ribbon_restart_at_extended_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ)
    (U : Ω → ℝ≥0 → ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (hc : ∀ ω, Continuous (γ ω)) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (C L : ℝ≥0) (ε κ v c : ℝ) (q : ℝ≥0∞) (S : Set C(ℝ≥0, ℂ))
    (hfiniteStep : ∀ (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0))) (E : Set Ω),
      (∀ᵐ ω ∂P, ω ∈ E → ActualRibbonAdmissible U γ G F C L ε κ v c S ω (σ ω)) →
      ∀ A : Set Ω, MeasurableSet[hσ.measurableSpace] A → A ⊆ E →
        q * P A ≤ P (A ∩ {ω | shiftedActualTrace γ hc ω (σ ω) ∈ S}))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (E : Set Ω) (hfinite : ∀ᵐ ω ∂P, ω ∈ E → τ ω ≠ ⊤)
    (hstate : ∀ᵐ ω ∂P, ω ∈ E →
      ActualRibbonAdmissible U γ G F C L ε κ v c S ω ((τ ω).untopD 0))
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) (hAE : A ⊆ E) :
    q * P A ≤ P (A ∩ {ω | shiftedActualTrace γ hc ω ((τ ω).untopD 0) ∈ S}) := by
  let Aₙ (n : ℕ) := A ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}
  have hmono : Monotone Aₙ := by
    intro n k hnk ω hω
    refine ⟨hω.1, ?_⟩
    change τ ω ≤ ((k : ℝ≥0) : WithTop ℝ≥0)
    exact hω.2.trans (WithTop.coe_le_coe.mpr (by exact_mod_cast hnk))
  have hcover : A =ᵐ[P] ⋃ n, Aₙ n := by
    filter_upwards [hfinite] with ω hω
    simp only [mem_iUnion]
    apply propext
    constructor
    · intro hωA
      lift τ ω to ℝ≥0 using hω (hAE hωA) with t ht
      obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
      refine ⟨n, hωA, ?_⟩
      change τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)
      rw [← ht]
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast hn)
    · rintro ⟨n, hn⟩
      exact hn.1
  have hlocal (n : ℕ) : q * P (Aₙ n) ≤
      P (A ∩ {ω | shiftedActualTrace γ hc ω ((τ ω).untopD 0) ∈ S}) := by
    let σ := cutoffStop τ (n : ℝ≥0)
    have hσ := cutoffStop_stopping ℱ τ hτ (n : ℝ≥0)
    let Eₙ := E ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}
    have hstateₙ : ∀ᵐ ω ∂P, ω ∈ Eₙ →
        ActualRibbonAdmissible U γ G F C L ε κ v c S ω (σ ω) := by
      filter_upwards [hstate] with ω hω hωE
      dsimp only [σ]
      rw [cutoffStop_eq_on_success τ _ ω hωE.2]
      exact hω hωE.1
    have hh := hfiniteStep σ hσ Eₙ hstateₙ (Aₙ n)
      (cutoffStop_success_measurable ℱ τ hτ _ A hA)
      (fun ω hω => ⟨hAE hω.1, hω.2⟩)
    apply hh.trans (measure_mono ?_)
    intro ω hω
    refine ⟨hω.1.1, ?_⟩
    have he : σ ω = (τ ω).untopD 0 := cutoffStop_eq_on_success τ _ ω hω.1.2
    simpa only [mem_ofPred_eq, he] using hω.2
  calc
    _ = q * P (⋃ n, Aₙ n) := by rw [measure_congr hcover]
    _ = ⨆ n, q * P (Aₙ n) := by rw [hmono.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ _ := iSup_le hlocal

/-- Actual adapted ribbon passages at the possibly infinite first-front
stops used by the dense experiment. The constants are the same uniform
constants obtained at finite stops from the published analytic inputs. -/
theorem uniform_conditional_actual_ribbon_step_extended
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (C L : ℝ≥0) (hC : 0 < C) (hL : 0 < L)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) :
    ∃ q c v₀ : ℝ, 0 < q ∧ 0 < c ∧ 0 < v₀ ∧
      ∀ (v : ℝ), 0 < v → v < v₀ → ∀ (τ : Ω → WithTop ℝ≥0)
      (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) τ),
      ∀ (S : Set C(ℝ≥0, ℂ)), MeasurableSet S → ∀ E : Set Ω,
      (∀ᵐ ω ∂P, ω ∈ E → τ ω ≠ ⊤) →
      (∀ᵐ ω ∂P, ω ∈ E → ActualRibbonAdmissible
        (fun ω t => Real.sqrt κ * B t ω) γ G F C L ε κ v c S ω ((τ ω).untopD 0)) →
      ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A → A ⊆ E →
        ENNReal.ofReal q * P A ≤ P (A ∩ {ω |
          shiftedActualTrace γ (fun ω => (hw ω).1) ω ((τ ω).untopD 0) ∈ S}) := by
  obtain ⟨q, c, v₀, hq, hcm, hv₀, hstep⟩ :=
    uniform_conditional_actual_ribbon_step P κ hκ hκ8 B hB hm hc γ G F hw
      hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW
      C L hC hL ε hε hεsmall
  refine ⟨q, c, v₀, hq, hcm, hv₀, ?_⟩
  intro v hv hvcut τ hτ S hS E hfinite hstate A hA hAE
  apply actual_ribbon_restart_at_extended_stop P _
    (fun ω t => Real.sqrt κ * B t ω) γ (fun ω => (hw ω).1) G F C L ε κ v c
    (ENNReal.ofReal q) S ?_ τ hτ E hfinite hstate A hA hAE
  intro σ hσ E' hstates A' hA' hAE'
  exact hstep v hv hvcut σ hσ S hS E' hstates A' hA' hAE'

end SLEExactGauge

end

end OAI
