import OAI.Probability.SLE.Gauge.ActualRibbonIteration

namespace OAI

/-! Uniform iteration of actual front-and-mass passages from explicit
analytic inputs, for any chart and number of steps satisfying the
deterministic ribbon bounds. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates Target

local instance publishedIterationPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance publishedIterationPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem uniform_actual_ribbon_iteration
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport μ γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (C L : ℝ≥0) (hC : 0 < C) (hL : 0 < L)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) :
    ∃ q c v₀ : ℝ, 0 < q ∧ q ≤ 1 ∧ 0 < c ∧ 0 < v₀ ∧
      ∀ (v : ℝ), 0 < v → v < v₀ → ∀ (P : ℂ → ℂ),
      Topology.IsClosedEmbedding (fun z : closedRibbon => P z) →
      ContinuousOn P closedRibbon → InjOn P closedRibbon → P 0 = 0 →
      (∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane) →
      Tendsto (fun t : ℝ => ‖P (t : ℂ)‖) atTop atTop →
      (∀ k : ℝ, LipschitzOnWith C P (ribbonStepPatch k)) →
      (∀ k : ℝ, ∀ z ∈ ribbonStepPatch k, ∀ w ∈ ribbonStepPatch k,
        dist z w ≤ L * dist (P z) (P w)) →
      ∀ (g : C(ℂ, ℝ)), (∀ z ∈ closedRibbon, g (P z) = z.re) → ∀ N : ℕ,
      (ENNReal.ofReal q) ^ N * μ (GoodRibbonPrefix γ (ribbonIntegerFront g γ 0) P ε) ≤
        μ (GoodRibbonPrefix γ (ribbonIntegerFront g γ 0) P ε ∩
          ⋂ n ∈ Finset.range N, actualRibbonSuccess γ g P ε κ v c n) := by
  obtain ⟨q, c, v₀, hq, hcm, hv₀, hstep⟩ :=
    uniform_conditional_actual_ribbon_step_extended μ κ hκ hκ8 B hB hm hc γ G F hw
      hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW
      C L hC hL ε hε hεsmall
  refine ⟨min q 1, c, v₀, lt_min hq (by norm_num), min_le_right _ _, hcm, hv₀, ?_⟩
  intro v hv hvcut P hemb hP hi hP0 hH hescape hu hl g hg N
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have ha : Adapted ℱ (fun t ω => γ ω t) := brownian_capacity_trace_adapted B hm hc κ γ G F hw
  have hγc : ∀ ω, Continuous (γ ω) := fun ω => (hw ω).1
  have hg0 (ω : Ω) : g (γ ω 0) = 0 := by
    rw [(hw ω).2.1, ← hP0]
    exact hg 0 (by constructor <;> norm_num)
  apply le_trans (mul_le_mul' (pow_le_pow_left'
    (ENNReal.ofReal_le_ofReal (min_le_left q 1)) N) le_rfl)
  apply actual_ribbon_successes_lower_bound μ ℱ γ ha hγc g hg0 P hemb ε κ v c
    (ENNReal.ofReal q) ?_ N
  intro n A hA hAE
  let k : ℝ := (n : ℝ) + 1
  have hk : 1 ≤ k := by dsimp only [k]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hτ := ribbonFrontStop_stopping ℱ g γ ha hγc k
  have hS := ribbonPathStep_measurable P C L ε k κ v c hplanar hεsmall hk hemb hP (hl k)
  have hb := actual_ribbon_step_on_good_prefix μ ℱ (fun ω t => Real.sqrt κ * B t ω)
    γ G F (fun ω => continuous_const.mul (hc ω)) hw C L hL ε κ v c hεsmall
    (ENNReal.ofReal q) P hemb hP hi hH hescape g hg hg0 k hk
    (fun j _ => hu j) (fun j _ => hl j) hτ
    (hstep v hv hvcut _ hτ _ hS) A hA hAE
  simpa only [actualRibbonSuccess, ribbonIntegerFront, k, Nat.cast_add, Nat.cast_one] using hb

end SLEExactGauge

end

end OAI
