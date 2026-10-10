import OAI.NumberTheory.JointDickman.Analysis.MellinLogWindows
import OAI.NumberTheory.JointDickman.Counting.ShortLengthComparison

namespace OAI

/-! # Freezing the relative short-window length on a small block -/
namespace JointDickman
open PublishedInputs

theorem shortAverage_le_fixed_logarithmic_window (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {X H ε x : ℝ} (hX : 0 < X) (hH : 1 ≤ H)
    (hx : x ∈ Set.Icc X ((1 + ε) * X)) :
    ‖complexShortAverage f H x‖ ≤
      ‖logarithmicWindowAverage f (Real.log ((X + H) / X)) (Real.log x)‖ +
        (3 * ε + 3 / H + H / X + 1 / X) := by
  have hx0 : 0 < x := hX.trans_le hx.1
  have hH0 : 0 < H := by linarith
  let K : ℝ := H * x / X
  have hK0 : 0 < K := div_pos (mul_pos hH0 hx0) hX
  have hHK : H ≤ K := by
    apply (le_div_iff₀ hX).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.1 hH0.le]
  have hKupper : K ≤ (1 + ε) * H := by
    apply (div_le_iff₀ hX).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.2 hH0.le]
  have hratio : (x + K) / x = (X + H) / X := by
    dsimp [K]
    field_simp
  have hlog := norm_shortAverage_le_logarithmic f hf hx0 hK0
  rw [hratio] at hlog
  have hdiff := shortAverage_length_difference f hf hx0.le hH hHK
  have herror : 3 * (K - H + 1) / H ≤ 3 * ε + 3 / H := by
    calc
      _ ≤ 3 * (ε * H + 1) / H := by gcongr; linarith
      _ = _ := by field_simp
  have hweight : (K + 1) / x = H / X + 1 / x := by
    dsimp [K]
    field_simp
  have hinv : 1 / x ≤ 1 / X := one_div_le_one_div_of_le hX hx.1
  calc
    _ = ‖(complexShortAverage f H x - complexShortAverage f K x) +
        complexShortAverage f K x‖ := by rw [sub_add_cancel]
    _ ≤ ‖complexShortAverage f H x - complexShortAverage f K x‖ +
        ‖complexShortAverage f K x‖ := norm_add_le _ _
    _ ≤ 3 * (K - H + 1) / H +
        (‖logarithmicWindowAverage f (Real.log ((X + H) / X)) (Real.log x)‖ +
          (K + 1) / x) := add_le_add hdiff hlog
    _ ≤ _ := by rw [hweight]; linarith

end JointDickman

end OAI
