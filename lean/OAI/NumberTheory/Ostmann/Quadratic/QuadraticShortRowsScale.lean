import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLongRows

namespace OAI

/-! # The initial exponent bound in the complementary row range -/

namespace Ostmann

theorem quadratic_short_rows_scale {ξ M N Y : ℝ} (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2)
    (hM : 0 < M) (hN : 0 < N) (hY : 1 ≤ Y) (hMN : M ≤ 4 * N * Y) :
    N ^ ξ ≤ 4 * Y * (M ^ (1 - ξ) * N ^ (2 * ξ - 1)) := by
  have hm : M ^ (1 - ξ) * M ^ (ξ - 1) = 1 := by
    rw [← Real.rpow_add hM]
    convert Real.rpow_zero M using 1
    congr 1
    ring
  have hn : N ^ (2 * ξ - 1) / N ^ (ξ - 1) = N ^ ξ := by
    rw [← Real.rpow_sub hN]
    congr 1
    ring
  have he : M ^ (1 - ξ) * N ^ (2 * ξ - 1) * (M / N) ^ (ξ - 1) = N ^ ξ := by
    rw [Real.div_rpow hM.le hN.le]
    calc
      _ = (M ^ (1 - ξ) * M ^ (ξ - 1)) * (N ^ (2 * ξ - 1) / N ^ (ξ - 1)) := by ring
      _ = _ := by rw [hm, hn, one_mul]
  have hratio : M / N ≤ 4 * Y := (div_le_iff₀ hN).mpr (by nlinarith)
  have hp : (M / N) ^ (ξ - 1) ≤ 4 * Y := by
    calc
      _ ≤ (4 * Y) ^ (ξ - 1) := Real.rpow_le_rpow (by positivity) hratio (by linarith)
      _ ≤ (4 * Y) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := Real.rpow_one _
  rw [← he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ M ^ (1 - ξ) * N ^ (2 * ξ - 1))

end Ostmann

end OAI
