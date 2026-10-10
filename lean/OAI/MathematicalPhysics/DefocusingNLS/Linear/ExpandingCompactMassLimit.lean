import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactFilterLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalFourier

namespace OAI

/-! # Compact physical mass of an unfiltered locally vanishing sequence -/

open Filter Topology MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance compactMassLimitMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance compactMassLimitProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem tendsto_expandingSample_product_mass (a k M R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (K : 𝓢(E, ℂ)) (hK : ∀ y : E, R < ‖y‖ → K y = 0) :
    Tendsto (fun n => ‖expandingPhysicalMassVector a k (L n) ha ha1 hk (hL n)
      (expandingProduct a k (L n) ha ha1 hk (hL n)
        (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)) (f n))‖)
      atTop (𝓝 0) := by
  have hb (n : ℕ) (y : E) :
      ‖expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n) (f n) y‖ ≤
        expandingEmbeddingBound a k * M :=
    (expandingPhysicalContinuous_norm_le a k (L n) ha ha1 hk (hL n) (f n) y).trans
      (mul_le_mul_of_nonneg_left (hf n) (by unfold expandingEmbeddingBound; positivity))
  have ht := tendsto_weightedL2_of_locally_uniform_zero (expandingEmbeddingBound a k * M)
    K (K.memLp 2) (fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n) (f n)) hb (by simpa only [expandingPhysicalContinuous_apply] using hlocal)
  have he : ∀ᶠ n in atTop, ‖expandingPhysicalMassVector a k (L n) ha ha1 hk (hL n)
      (expandingProduct a k (L n) ha ha1 hk (hL n)
        (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)) (f n))‖ ^ 2 =
      ∫ y : E, ‖K y * expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n) (f n) y‖ ^ 2 := by
    filter_upwards [hLinf.eventually (eventually_ge_atTop R)] with n hn
    rw [← LinearIsometryEquiv.norm_map torusFourierIsometry,
      expandingPhysicalMassVector_isometry, expandingUnitTorusFunction_product,
      torusPhysicalL2Value_norm_sq]
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
