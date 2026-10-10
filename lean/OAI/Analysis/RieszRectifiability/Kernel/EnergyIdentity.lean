import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem cutoff_energy_identity (u v a b : ℝ) :
    (u - v) * (a ^ 2 * u - b ^ 2 * v) =
      (a * u - b * v) ^ 2 - u * v * (a - b) ^ 2 := by
  ring

theorem centered_coordinate_difference (u v c : ℝ) :
    (u - c) - (v - c) = u - v := by
  ring

theorem normal_coordinate_difference {d : ℕ} (e z x y : Ambient d) :
    inner ℝ e (x - z) - inner ℝ e (y - z) = inner ℝ e (x - y) := by
  simp only [inner_sub_right]
  ring

theorem cutoff_square_eq_pairing_add_error (u v a b : ℝ) :
    (a * u - b * v) ^ 2 =
      (u - v) * (a ^ 2 * u - b ^ 2 * v) + u * v * (a - b) ^ 2 := by
  ring

end

end RieszRectifiability

end OAI
