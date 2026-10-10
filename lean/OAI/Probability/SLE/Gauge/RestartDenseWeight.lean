import OAI.Probability.SLE.Mass.RestartStoppedMass
import OAI.Probability.SLE.Gauge.CanonicalDenseSections

namespace OAI

/-! A successful canonical dense section, multiplied by its exact centered
weight, contributes to the actual physical stopped-mass event. This proves
the pointwise density domination needed in conditional section integration. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open FrontSuccessMeasurability

local instance denseWeightRealMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance denseWeightRealBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance denseWeightComplexMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance denseWeightComplexBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma IsCapacityTwoWitness.normalized_restart_dense_weight_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T a : ℝ≥0) (ha : 0 < a)
    (κ : ℝ) (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ)) (p : C(ℝ≥0, ℝ))
    (hb : IsCapacityTwoWitness (normalizedRestartDriver U T a) (Φ p) G' F')
    (hdriver : (fun t => Real.sqrt κ * p t) = normalizedRestartDriver U T a)
    (w : ℂ) (hwH : w ∈ upperHalfPlane) (u q : ℝ) (hq : 0 ≤ q)
    (hbase : fullRadius G T (F T ((a : ℂ) * w + (U T : ℂ))) =
      (2 * (F T ((a : ℂ) * w + (U T : ℂ))).im) * Real.exp (-u))
    (Fb : C(closedHalfPlane, ℂ))
    (hpath : ∀ t, finiteBoundaryPath Fb (Φ p) t = γ (T + a ^ 2 * t))
    (b r v : ℝ) (m : ℕ) :
    (canonicalDenseEvent κ Φ Fb q w b r m v (F T ((a : ℂ) * w + (U T : ℂ)))).indicator
      (fun p => ENNReal.ofReal
          (greenDensity κ U γ G T (F T ((a : ℂ) * w + (U T : ℂ))) /
            initialGreen κ (F T ((a : ℂ) * w + (U T : ℂ)))) *
        canonicalFiniteDensity κ (q, w, p)) p ≤
      if ENNReal.ofReal (b * r ^ dimension κ * (m : ℝ) ^ codimension κ) ≤
          stoppedWholeSausageCharge κ ⟨γ, hw.1⟩
            (radiusLevelTime γ G (F T ((a : ℂ) * w + (U T : ℂ))) (u + q)) v
            (closedBall (F T ((a : ℂ) * w + (U T : ℂ))) r) then
        ENNReal.ofReal (stoppedGreen κ U γ G (F T ((a : ℂ) * w + (U T : ℂ))) (u + q) /
          initialGreen κ (F T ((a : ℂ) * w + (U T : ℂ))))
      else 0 := by
  classical
  have hb' : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) (Φ p) G' F' := hdriver ▸ hb
  have hzH : (a : ℂ) * w + (U T : ℂ) ∈ upperHalfPlane := by
    change 0 < ((a : ℂ) * w + (U T : ℂ)).im
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.mul_im,
      Complex.ofReal_re, zero_mul] using mul_pos (show 0 < (a : ℝ) from ha) hwH
  have hphysH := (hw.2.2.2.2.2.2.1 T hzH).1.1
  by_cases hC : p ∈ canonicalDenseEvent κ Φ Fb q w b r m v (F T ((a : ℂ) * w + (U T : ℂ)))
  · rw [indicator_of_mem hC, canonicalFiniteDensity_eq κ p hb' q hq w]
    by_cases hfinite : radiusLevelTime (Φ p) G' w q < ∞
    · have hmass := hw.normalized_restart_stopped_mass_le hU T a ha hb w u q hbase
        (finiteBoundaryPath Fb (Φ p)) hpath hfinite κ v
        (closedBall (F T ((a : ℂ) * w + (U T : ℂ))) r)
      have hcanon := canonicalRadiusLevel_eq κ p hb' q hq w
      have hC' : ENNReal.ofReal (b * r ^ dimension κ * (m : ℝ) ^ codimension κ) ≤
          stoppedWholeSausageCharge κ (finiteBoundaryPath Fb (Φ p))
            (radiusLevelTime (Φ p) G' w q) v (closedBall (F T ((a : ℂ) * w + (U T : ℂ))) r) := by
        simpa only [canonicalDenseEvent, mem_ofPred_eq, hcanon] using hC
      rw [ite_eq_left (hC'.trans hmass)]
      rw [hdriver, ← ENNReal.ofReal_mul
        (div_nonneg (greenDensity_nonneg hw κ T _) (initialGreen_pos κ _ hphysH).le)]
      apply ENNReal.ofReal_le_ofReal
      have hbound := hw.normalized_restart_stopped_green_lower hU T a ha hb κ w hwH u q hbase
      calc
        _ = (greenDensity κ U γ G T (F T ((a : ℂ) * w + (U T : ℂ))) *
          (stoppedGreen κ (normalizedRestartDriver U T a) (Φ p) G' w q / initialGreen κ w)) /
          initialGreen κ (F T ((a : ℂ) * w + (U T : ℂ))) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hbound (initialGreen_pos κ _ hphysH).le
    · rw [hdriver, stoppedGreen, ite_eq_right hfinite, zero_div, ENNReal.ofReal_zero, mul_zero]
      exact bot_le
  · rw [indicator_of_notMem hC]
    exact bot_le

end SLEExactGauge

end

end OAI
