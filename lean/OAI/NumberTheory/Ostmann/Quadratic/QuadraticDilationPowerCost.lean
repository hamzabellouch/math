import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBalancedExponent

namespace OAI

/-! # The enlarged balanced row interval costs only a small power -/

namespace Ostmann

theorem quadratic_dilation_power_cost {ξ δ a D M N L : ℝ}
    (hξ : 1 ≤ ξ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (ha : 0 ≤ a) (hD : 1 ≤ D)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hL : N ^ quadraticImprovedExponent ξ ≤ L)
    (hLu : L ≤ D * (2 * M * N) ^ δ * (M + N ^ quadraticImprovedExponent ξ)) :
    (L * N) ^ a * (L + L ^ (1 - ξ) * N ^ (2 * ξ - 1)) ≤
      (3 * D * (4 * D) ^ a) * (M * N) ^ (4 * a + δ) *
        (M + N ^ quadraticImprovedExponent ξ) := by
  let X := M * N
  let H := M + N ^ quadraticImprovedExponent ξ
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hXp : 0 < X := mul_pos hMp hNp
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hM hN
  have hHp : 0 < H := by dsimp [H]; positivity
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hMX : M ≤ X := le_mul_of_one_le_right hMp.le hN
  have hNX : N ≤ X := le_mul_of_one_le_left hNp.le hM
  have hH : H ≤ 2 * X ^ 2 := by
    have hp := Real.rpow_le_rpow_of_exponent_le hN (quadratic_improved_exponent_bounds hξ).2
    rw [Real.rpow_two] at hp
    have hs := pow_le_pow_left₀ hNp.le hNX 2
    have hXX := le_self_pow₀ hX (by norm_num : (2 : ℕ) ≠ 0)
    dsimp [H]
    nlinarith
  have htwoX : 1 ≤ 2 * X := by linarith
  have hLpoly : L ≤ 4 * D * X ^ 3 := by
    have hp : (2 * X) ^ δ ≤ 2 * X := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le htwoX hδ'
    calc
      _ ≤ D * (2 * X) ^ δ * H := by simpa only [X, H, mul_assoc] using hLu
      _ ≤ D * (2 * X) * (2 * X ^ 2) := by gcongr
      _ = _ := by ring
  have hLN : L * N ≤ 4 * D * X ^ 4 := by
    calc
      _ ≤ (4 * D * X ^ 3) * X := mul_le_mul hLpoly hNX hNp.le (by positivity)
      _ = _ := by ring
  have hmass : L + L ^ (1 - ξ) * N ^ (2 * ξ - 1) ≤ 3 * D * X ^ δ * H := by
    have hs := quadratic_balanced_row_power hξ hNp hL
    have htwo : (2 : ℝ) ^ δ ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hδ'
    have hpow : 1 ≤ X ^ δ := Real.one_le_rpow hX hδ
    have hsum : N ^ quadraticImprovedExponent ξ ≤ X ^ δ * H := by
      have hh : N ^ quadraticImprovedExponent ξ ≤ H := le_add_of_nonneg_left hMp.le
      exact hh.trans (le_mul_of_one_le_left hHp.le hpow)
    have hLshort : L ≤ 2 * D * X ^ δ * H := by
      calc
        _ ≤ D * (2 * X) ^ δ * H := by simpa only [X, H, mul_assoc] using hLu
        _ = D * (2 ^ δ * X ^ δ) * H := by rw [Real.mul_rpow (by norm_num) hXp.le]
        _ = (D * X ^ δ * H) * 2 ^ δ := by ring
        _ ≤ (D * X ^ δ * H) * 2 := mul_le_mul_of_nonneg_left htwo (by positivity)
        _ = _ := by ring
    have hDX := mul_le_mul_of_nonneg_right hD (show 0 ≤ X ^ δ * H by positivity)
    nlinarith only [hs, hsum, hLshort, hDX]
  have hpower : (L * N) ^ a ≤ (4 * D) ^ a * X ^ (4 * a) := by
    calc
      _ ≤ (4 * D * X ^ 4) ^ a := Real.rpow_le_rpow (by positivity) hLN ha
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        rw [← Real.rpow_natCast X 4, ← Real.rpow_mul hXp.le]
        norm_num
  calc
    _ ≤ ((4 * D) ^ a * X ^ (4 * a)) * (3 * D * X ^ δ * H) :=
      mul_le_mul hpower hmass (by positivity) (by positivity)
    _ = _ := by
      change _ = (3 * D * (4 * D) ^ a) * X ^ (4 * a + δ) * H
      rw [Real.rpow_add hXp]
      ring

end Ostmann

end OAI
