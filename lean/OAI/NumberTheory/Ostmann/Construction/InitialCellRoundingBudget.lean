import OAI.NumberTheory.Ostmann.Construction.SelectedInitialTotal

namespace OAI

/-! # The initial cell rounding fits in the fixed gap reserve -/
namespace Ostmann

theorem initial_cell_rounding_budget (k : ℕ) (R D L : ℝ)
    (hk : 2 ≤ k) (hR : 0 ≤ R) (hL : 1 ≤ L) (hD : D ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L) :
    (6 + 4 * k) * (64 * D + 1) + 2 * ((3 + 2 * k : ℕ) + 3) ≤
      (spectatorBulkCount k L : ℝ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  have hcoef : (6 + 4 * (k : ℝ)) * (64 * R + 3) ≤ (k : ℝ) ^ 4 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hlarge hk0
    nlinarith only [hh, hk2, hR]
  have herr : (6 + 4 * k) * (64 * D + 1) + 2 * ((3 + 2 * k : ℕ) + 3) ≤
      (6 + 4 * (k : ℝ)) * (64 * R + 3) * L := by
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hD (show 0 ≤ 64 * (6 + 4 * (k : ℝ)) by positivity),
      mul_le_mul_of_nonneg_left hL (show 0 ≤ 18 + 12 * (k : ℝ) by positivity), hk0]
  apply herr.trans
  calc
    _ ≤ (k : ℝ) ^ 4 / 2 * L := mul_le_mul_of_nonneg_right hcoef hL0
    _ = (k : ℝ) ^ 4 * L / 2 := by ring
    _ ≤ _ := spectatorBulkCount_half k L hscale

end Ostmann

end OAI
