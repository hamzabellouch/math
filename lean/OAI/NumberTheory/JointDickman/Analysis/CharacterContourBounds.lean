import OAI.NumberTheory.JointDickman.Analysis.CharacterContourSeries

namespace OAI

/-! # Small-power bounds for the continued character series -/
namespace JointDickman
open Complex

theorem characterContourSeries_small_power {z η : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ (f : ℂ → ℂ) (s : ℂ), 1-η/2 ≤ s.re →
      Complex.exp (f s) = χ.LFunction s →
      ‖characterContourSeries χ z f s‖ ≤ C * (((q:ℝ)+2)*(‖s‖+2))^η := by
  obtain ⟨G,hG,hGb⟩ := squarefreeCharacterAnalyticFactor_uniform_bound hz hz1
    (by norm_num : (1/2:ℝ) < 3/4)
  obtain ⟨K,hK,hKb⟩ := LargePrimeGaps.LFunction_norm_small_power
    (show 0 < η/2 by positivity) (show η/2 ≤ 1/2 by linarith)
  let B := max 1 K
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨G*B, mul_pos hG (lt_of_lt_of_le zero_lt_one hB), ?_⟩
  intro q _ χ hn f s hs he
  let W : ℝ := ((q:ℝ)+2)*(‖s‖+2)
  have hW : 1 ≤ W := by dsimp [W]; nlinarith [Nat.cast_nonneg (α := ℝ) q, norm_nonneg s]
  have hWp : 1 ≤ W^η := Real.one_le_rpow hW hη.le
  have hBW : 1 ≤ B*W^η := one_le_mul_of_one_le_of_one_le hB hWp
  have hL : ‖χ.LFunction s‖ ≤ B*W^η := by
    have hb := hKb q χ hn s hs
    rw [show 2*(η/2) = η by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right 1 K) (Real.rpow_nonneg (by linarith) _))
  calc
    _ ≤ G*‖χ.LFunction s‖^z := characterContourSeries_norm_le χ
      (fun t ht => hGb χ t ht) (by linarith) he
    _ ≤ G*(B*W^η)^z := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hL hz) hG.le
    _ ≤ G*(B*W^η) := mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hBW hz1) hG.le
    _ = (G*B)*W^η := by ring

/-- On a fixed-height rectangle the bound depends on the height and modulus only. -/
theorem characterContourSeries_rectangle_bound {z η : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ (f : ℂ → ℂ) (T : ℝ), 0 ≤ T → ∀ s : ℂ,
      1-η/2 ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
      Complex.exp (f s) = χ.LFunction s →
      ‖characterContourSeries χ z f s‖ ≤ C * (((q:ℝ)+2)*(T+2))^η := by
  obtain ⟨C,hC,hb⟩ := characterContourSeries_small_power hz hz1 hη hη1
  refine ⟨C*2^η, by positivity, ?_⟩
  intro q _ χ hn f T hT s hs hs2 hi he
  have hs0 : 0 ≤ s.re := by linarith
  have hnS : ‖s‖+2 ≤ 2*(T+2) := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hs0] at hh
    linarith
  have hbase : ((q:ℝ)+2)*(‖s‖+2) ≤ 2*(((q:ℝ)+2)*(T+2)) := by
    nlinarith [mul_le_mul_of_nonneg_left hnS (show (0:ℝ) ≤ q+2 by positivity)]
  calc
    _ ≤ C*(((q:ℝ)+2)*(‖s‖+2))^η := hb q χ hn f s hs he
    _ ≤ C*(2*(((q:ℝ)+2)*(T+2)))^η := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hbase hη.le) hC.le
    _ = (C*2^η)*(((q:ℝ)+2)*(T+2))^η := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      ring

end JointDickman

end OAI
