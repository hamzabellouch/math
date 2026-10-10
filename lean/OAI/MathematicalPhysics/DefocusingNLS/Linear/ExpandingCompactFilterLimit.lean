import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingGeneralFilterLimit

namespace OAI

/-! # Compact physical multiplication after each fixed Schwartz filter -/

open Filter Topology MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance expandingCompactFilterMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance expandingCompactFilterProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem tendsto_expandingCompactPhysical_filter (a k M R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (J K : 𝓢(E, ℂ)) (hK : ∀ y : E, R < ‖y‖ → K y = 0) :
    Tendsto (fun n => ‖torusPhysicalL2Value (L n)
      (expandingUnitTorusFunction a k (L n)
          (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)) *
        expandingUnitTorusFunction a k (L n) (expandingSchwartzFilter (L n) J (f n)))‖)
      atTop (𝓝 0) := by
  have ht := tendsto_expandingSchwartzFilter_weightedL2 a k M ha ha1 hk L hL f hf hlocal J K (K.memLp 2)
  have he : ∀ᶠ n in atTop, ‖torusPhysicalL2Value (L n)
      (expandingUnitTorusFunction a k (L n)
          (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)) *
        expandingUnitTorusFunction a k (L n) (expandingSchwartzFilter (L n) J (f n)))‖ ^ 2 =
      ∫ y : E, ‖K y * expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
        (expandingSchwartzFilter (L n) J (f n)) y‖ ^ 2 := by
    filter_upwards [hLinf.eventually (eventually_ge_atTop R)] with n hn
    rw [torusPhysicalL2Value_norm_sq]
    simp only [ContinuousMap.mul_apply]
    apply expandingCompactWeight_integral a k (L n) R ha ha1 hk (hL n) _ K hK
    calc
      2 * R ≤ 2 * L n := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ < 2 * Real.pi * L n := mul_lt_mul_of_pos_right
        (by linarith [Real.pi_gt_three] : (2 : ℝ) < 2 * Real.pi) (by linarith [hL n])
  have hs := ht.congr' (he.mono fun _ hn => hn.symm)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

end DefocusingNLS

end OAI
