import OAI.Combinatorics.EditApproximation.Binary.BinaryCellGrid
import OAI.Combinatorics.EditApproximation.Binary.BinaryMedianKernel
import OAI.Combinatorics.EditApproximation.Geometry.Accuracy
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Clamp the final value to the input length and round down by binary division. -/


theorem finalAnswerWithWork_value (N : ℕ) (a : BinaryFraction) :
    bitWordValue (finalAnswerWithWork N a).1 = integerAnswer N (a.value : ℝ) := by
  have hfloor : ⌊(a.value : ℝ)⌋₊ = ⌊a.value⌋₊ := by
    apply Nat.floor_congr
    intro n
    norm_cast
  simp only [finalAnswerWithWork, wordMinWithWork_value, bitWordValue_bits, naturalFloorWithWork_value]
  rw [← hfloor]
  unfold integerAnswer
  by_cases hn : a.value ≤ 0
  · have hnR : (a.value : ℝ) ≤ 0 := by exact_mod_cast hn
    rw [Nat.floor_of_nonpos hnR, min_eq_right (Nat.zero_le N)]
    have hm : min (N : ℝ) (a.value : ℝ) ≤ 0 := (min_le_right _ _).trans hnR
    rw [max_eq_left hm, Nat.floor_zero]
  · have hnR : 0 ≤ (a.value : ℝ) := by exact_mod_cast (le_of_not_ge hn)
    have hm : 0 ≤ min (N : ℝ) (a.value : ℝ) := le_min (Nat.cast_nonneg _) hnR
    rw [max_eq_right hm]
    by_cases hN : (a.value : ℝ) ≤ N
    · have hf : ⌊(a.value : ℝ)⌋₊ ≤ N := by
        simpa only [Nat.floor_natCast] using Nat.floor_mono hN
      rw [min_eq_right hN, min_eq_right hf]
    · have hf : N ≤ ⌊(a.value : ℝ)⌋₊ := Nat.le_floor (le_of_not_ge hN)
      rw [min_eq_left (le_of_not_ge hN), Nat.floor_natCast, min_eq_left hf]

theorem finalAnswerWithWork_cost (N : ℕ) (a : BinaryFraction) :
    (finalAnswerWithWork N a).2 ≤ 400 * (a.width + Nat.size N + 1) ^ 2 := by
  have hf := (naturalFloorWithWork_bounds a).2
  have hl := (naturalFloorWithWork_bounds a).1
  have hc := wordLEWithWork_cost N.bits (naturalFloorWithWork a).1
  rw [Nat.size_eq_bits_len] at hc
  have hpoly := Nat.pow_le_pow_left (show a.width + 1 ≤ a.width + Nat.size N + 1 by omega) 2
  unfold finalAnswerWithWork wordMinWithWork
  dsimp only
  nlinarith only [hf, hl, hc, hpoly, Nat.zero_le a.width, Nat.zero_le (Nat.size N),
    sq_nonneg (a.width + Nat.size N)]

end BinaryFraction
end EditApproximation

end OAI
