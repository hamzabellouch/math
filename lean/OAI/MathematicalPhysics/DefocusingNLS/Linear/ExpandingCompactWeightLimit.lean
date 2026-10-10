import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactWeightIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFilteredWeightedLimit

namespace OAI

/-! # Compactly supported torus coefficients annihilate localized weak-null filtered data -/

open Filter Topology MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance expandingCompactLimitMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance expandingCompactLimitProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem tendsto_expandingCompactWeight_derivative (a k M R S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hS : 0 < S)
    (N : ℕ) (j : Fin N → Fin 12) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (hLinf : Tendsto L atTop atTop) (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (K : 𝓢(E, ℂ)) (hK : ∀ y : E, R < ‖y‖ → K y = 0) :
    Tendsto (fun n => (2 * Real.pi * L n) ^ 12 * (∫ x : T,
      ‖expandingUnitTorusFunction a k (L n)
          (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)) x *
        expandingUnitTorusFunction a k (L n)
          (expandingSmoothDerivative (L n) S hS N j (f n)) x‖ ^ 2)) atTop (𝓝 0) := by
  have ht := tendsto_expandingSmoothDerivative_weightedL2 a k M S ha ha1 hk hS N j
    L hL f hf hlocal K (K.memLp 2)
  have he : ∀ᶠ n in atTop, (2 * Real.pi * L n) ^ 12 * (∫ x : T,
      ‖expandingUnitTorusFunction a k (L n)
          (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)) x *
        expandingUnitTorusFunction a k (L n)
          (expandingSmoothDerivative (L n) S hS N j (f n)) x‖ ^ 2) =
      ∫ y : E, ‖K y * expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
        (expandingSmoothDerivative (L n) S hS N j (f n)) y‖ ^ 2 := by
    filter_upwards [hLinf.eventually (eventually_ge_atTop R)] with n hn
    apply expandingCompactWeight_integral a k (L n) R ha ha1 hk (hL n) _ K hK
    calc
      2 * R ≤ 2 * L n := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ < 2 * Real.pi * L n := mul_lt_mul_of_pos_right
        (by linarith [Real.pi_gt_three] : (2 : ℝ) < 2 * Real.pi) (by linarith [hL n])
  exact ht.congr' (he.mono fun _ hn => hn.symm)

end DefocusingNLS

end OAI
