import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingApproximationLinear
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProductDifference

namespace OAI

/-! # Compact coefficient approximation is preserved by the actual torus product -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem ExpandingCompactApproximation.mul (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (q r : ℕ → FourierL2) (hq : ExpandingCompactApproximation a k ha1 hk L hL q)
    (hr : ExpandingCompactApproximation a k ha1 hk L hL r)
    (hqb : ∀ n, ‖q n‖ ≤ M) (hrb : ∀ n, ‖r n‖ ≤ M) :
    ExpandingCompactApproximation a k ha1 hk L hL
      (fun n => expandingProduct a k (L n) ha ha1 hk (hL n) (q n) (r n)) := by
  have hM : 0 ≤ M := (norm_nonneg (q 0)).trans (hqb 0)
  let A := expandingAlgebraBound a k
  have hA : 0 ≤ A := expandingAlgebraBound_nonneg a k
  let C := A * (2 * M + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  intro ε hε
  let δ := min 1 (ε / (C + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (C + 1) ≤ ε := (le_div_iff₀ (by positivity : 0 < C + 1)).mp (min_le_right _ _)
  obtain ⟨R, K, hK, heq⟩ := hq δ hδ
  obtain ⟨S, J, hJ, her⟩ := hr δ hδ
  let T := max R S
  have hKT : ∀ y : E, T < ‖y‖ → K y = 0 := fun y hy => hK y ((le_max_left R S).trans_lt hy)
  have hJT : ∀ y : E, T < ‖y‖ → J y = 0 := fun y hy => hJ y ((le_max_right R S).trans_lt hy)
  refine ⟨T, SchwartzMap.smulLeftCLM ℂ K J, ?_, ?_⟩
  · intro y hy
    rw [SchwartzMap.smulLeftCLM_apply_apply K.hasTemperateGrowth, hKT y hy, zero_smul]
  · filter_upwards [heq, her, hLinf.eventually (eventually_ge_atTop T)] with n hnq hnr hnL
    have hsep : 2 * T < 2 * Real.pi * L n := calc
      2 * T ≤ 2 * L n := mul_le_mul_of_nonneg_left hnL (by norm_num)
      _ < 2 * Real.pi * L n := mul_lt_mul_of_pos_right
        (by linarith [Real.pi_gt_three] : (2 : ℝ) < 2 * Real.pi) (by linarith [hL n])
    rw [← schwartzTorusSample_product a k (L n) T ha ha1 hk (hL n) hsep K J hKT hJT]
    have hKB : ‖schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)‖ ≤ M + 1 := by
      calc
        _ ≤ ‖schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K) - q n‖ + ‖q n‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ δ + M := add_le_add (by rw [norm_sub_rev]; exact hnq.le) (hqb n)
        _ ≤ M + 1 := by linarith
    have hb := expandingProduct_difference_norm a k (L n) ha ha1 hk (hL n) (q n) (r n)
      (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K))
      (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel J))
    calc
      _ ≤ A * (‖q n - schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)‖ * ‖r n‖ +
        ‖schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)‖ *
          ‖r n - schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel J)‖) := hb
      _ ≤ A * (δ * M + (M + 1) * δ) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul hnq.le (hrb n) (norm_nonneg _) hδ.le)
          (mul_le_mul hKB hnr.le (norm_nonneg _) (by linarith))) hA
      _ = C * δ := by dsimp [C]; ring
      _ < ε := by nlinarith

end DefocusingNLS

end OAI
