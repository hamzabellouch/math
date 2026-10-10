import OAI.Probability.SLE.Gauge.SerpentineNormalizedMass
import OAI.Probability.SLE.Gauge.DenseRibbonNumerics

namespace OAI

/-! The concrete stopped dense experiment costs at most exponentially
in m²; the constants are independent of the marked point and mesh. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates Target

theorem uniform_serpentine_exponential_stopped_mass
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport μ γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) :
    ∃ c v₀ : ℝ, 0 < c ∧ 0 < v₀ ∧ ∀ s : ℝ, 0 < s →
      ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, 0 < v → v < v₀ →
      ∀ w : ℂ, ‖w‖ ≤ 1 → s ≤ w.im → ∀ m : ℕ, 0 < m → ∀ g : C(ℂ, ℝ),
      (∀ z ∈ closedRibbon, g (experimentChart s w m z) = z.re) →
      ENNReal.ofReal (Real.exp (-C * (m : ℝ) ^ 2)) ≤ μ {ω |
        ω ∈ GoodRibbonPrefix γ (ribbonIntegerFront g γ (experimentSteps s w m)) (experimentChart s w m) ε ∧
        ((m ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal c ≤ segmentSausageCharge κ (γ ω) 0
          ((ribbonIntegerFront g γ (experimentSteps s w m) ω).untopD 0) v (normalizedExperimentDisk s w m)} := by
  obtain ⟨q₀, q, c, v₀, hq₀, hq₀1, hq, hq1, hcm, hv₀, hprob⟩ :=
    uniform_serpentine_normalized_stopped_mass μ κ hκ hκ8 B hB hm hc γ G F hw
      hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW ε hε hεsmall
  have hq₀fin : q₀ ≠ ⊤ := ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hq₀1
  have hp : 0 < q₀.toReal := ENNReal.toReal_pos hq₀.ne' hq₀fin
  refine ⟨c, v₀, hcm, hv₀, fun s hs => ?_⟩
  let D := fitEntryBound s + 601 + 100 * Real.pi
  have hD : 0 ≤ D := by dsimp only [D]; linarith [fitEntryBound_pos hs, Real.pi_pos]
  obtain ⟨C, hC, hcost⟩ := ribbon_initial_and_steps_quadratic_cost hq hq1 hp hD
  refine ⟨C, hC, fun v hv hvcut w hwn hwy m hmp g hg => ?_⟩
  have hcount : (experimentSteps s w m : ℝ) ≤ D * (m : ℝ) ^ 2 := by
    apply le_trans (Nat.cast_le.mpr (Nat.sub_le _ 1))
    exact fit_completion_quadratic hs w hwn hwy hmp
  have hreal := hcost m (experimentSteps s w m) hmp hcount
  have hENN := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (pow_nonneg hq.le _), ENNReal.ofReal_pow hq.le,
    ENNReal.ofReal_toReal hq₀fin] at hENN
  exact hENN.trans (hprob v hv hvcut s hs w hwy m hmp g hg)

end SLEExactGauge.Serpentine

end

end OAI
