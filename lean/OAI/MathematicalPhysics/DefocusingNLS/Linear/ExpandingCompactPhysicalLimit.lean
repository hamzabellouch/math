import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactWeightLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusPhysicalL2

namespace OAI

/-! # Norm compactness of the sampled coefficient times filtered derivatives -/

open Filter Topology MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance expandingCompactPhysicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance expandingCompactPhysicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem tendsto_expandingCompactPhysical_derivative (a k M R S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hS : 0 < S)
    (N : ℕ) (j : Fin N → Fin 12) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (hLinf : Tendsto L atTop atTop) (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (K : 𝓢(E, ℂ)) (hK : ∀ y : E, R < ‖y‖ → K y = 0) :
    Tendsto (fun n => ‖torusPhysicalL2Value (L n)
      (expandingUnitTorusFunction a k (L n)
          (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)) *
        expandingUnitTorusFunction a k (L n)
          (expandingSmoothDerivative (L n) S hS N j (f n)))‖) atTop (𝓝 0) := by
  have ht := tendsto_expandingCompactWeight_derivative a k M R S ha ha1 hk hS N j
    L hL hLinf f hf hlocal K hK
  have hs : Tendsto (fun n => ‖torusPhysicalL2Value (L n)
      (expandingUnitTorusFunction a k (L n)
          (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)) *
        expandingUnitTorusFunction a k (L n)
          (expandingSmoothDerivative (L n) S hS N j (f n)))‖ ^ 2) atTop (𝓝 0) := by
    simpa only [torusPhysicalL2Value_norm_sq, ContinuousMap.mul_apply] using ht
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

end DefocusingNLS

end OAI
