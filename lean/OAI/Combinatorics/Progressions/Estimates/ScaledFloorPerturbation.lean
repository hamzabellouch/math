import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem scaled_floor_perturbation {s a ε : ℝ} (hs : 0 < s)
    (z : ℤ) (hz : |(z : ℝ)| ≤ ε * s) :
    |((⌊s * a⌋ + z : ℤ) : ℝ) / s - a| ≤ ε + 1 / s := by
  have hround : |(⌊s * a⌋ : ℝ) - s * a| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [Int.floor_le (s * a), Int.lt_floor_add_one (s * a)]
  have hsum : |((⌊s * a⌋ + z : ℤ) : ℝ) - s * a| ≤ 1 + ε * s := by
    rw [Int.cast_add, show (⌊s * a⌋ : ℝ) + z - s * a =
      ((⌊s * a⌋ : ℝ) - s * a) + z by ring]
    exact (abs_add_le _ _).trans (add_le_add hround hz)
  have heq : ((⌊s * a⌋ + z : ℤ) : ℝ) / s - a =
      (((⌊s * a⌋ + z : ℤ) : ℝ) - s * a) / s := by
    field_simp
  rw [heq, abs_div, abs_of_pos hs]
  calc
    _ ≤ (1 + ε * s) / s := div_le_div_of_nonneg_right hsum hs.le
    _ = ε + 1 / s := by field_simp; ring

theorem scaled_floor_perturbation_le_twice {s a ε : ℝ} (hs : 0 < s)
    (hscale : 1 / s ≤ ε) (z : ℤ) (hz : |(z : ℝ)| ≤ ε * s) :
    |((⌊s * a⌋ + z : ℤ) : ℝ) / s - a| ≤ 2 * ε := by
  have h := scaled_floor_perturbation (a := a) hs z hz
  linarith

end Erdos3

end

end OAI
