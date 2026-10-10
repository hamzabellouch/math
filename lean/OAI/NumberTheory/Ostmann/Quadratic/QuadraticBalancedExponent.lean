import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicDilation

namespace OAI

/-! # The balanced exponent and an explicit enlarged row cutoff -/

namespace Ostmann

noncomputable def quadraticImprovedExponent (ξ : ℝ) : ℝ := 2 - 1 / ξ

theorem quadratic_improved_exponent_bounds {ξ : ℝ} (hξ : 1 ≤ ξ) :
    1 ≤ quadraticImprovedExponent ξ ∧ quadraticImprovedExponent ξ ≤ 2 := by
  have hpos : 0 < ξ := by linarith
  have hdiv : 1 / ξ ≤ 1 := (div_le_one hpos).mpr hξ
  unfold quadraticImprovedExponent
  constructor <;> linarith [one_div_pos.mpr hpos]

theorem quadratic_improved_exponent_balance {ξ : ℝ} (hξ : 0 < ξ) :
    quadraticImprovedExponent ξ * ξ = 2 * ξ - 1 := by
  unfold quadraticImprovedExponent
  field_simp

theorem quadratic_balanced_row_power {ξ N L : ℝ} (hξ : 1 ≤ ξ) (hN : 0 < N)
    (hL : N ^ quadraticImprovedExponent ξ ≤ L) :
    L ^ (1 - ξ) * N ^ (2 * ξ - 1) ≤ N ^ quadraticImprovedExponent ξ := by
  have hp : 0 < N ^ quadraticImprovedExponent ξ := Real.rpow_pos_of_pos hN _
  calc
    _ ≤ (N ^ quadraticImprovedExponent ξ) ^ (1 - ξ) * N ^ (2 * ξ - 1) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hp hL (by linarith)) (by positivity)
    _ = N ^ quadraticImprovedExponent ξ := by
      rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
      congr 1
      have hh := quadratic_improved_exponent_balance (by linarith : 0 < ξ)
      nlinarith

noncomputable def quadraticDilationCutoff (C δ p : ℝ) (M N : ℕ) : ℕ :=
  ⌈C * (2 * (M : ℝ) * N) ^ δ * max 1 ((N : ℝ) ^ p / M)⌉₊

theorem quadratic_dilation_cutoff_bounds {C δ p : ℝ} (hC : 1 ≤ C) (hδ : 0 ≤ δ)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    C * (2 * (M : ℝ) * N) ^ δ ≤ quadraticDilationCutoff C δ p M N ∧
      (N : ℝ) ^ p ≤ ((quadraticDilationCutoff C δ p M N * M : ℕ) : ℝ) ∧
      ((quadraticDilationCutoff C δ p M N * M : ℕ) : ℝ) ≤
        (C + 1) * (2 * (M : ℝ) * N) ^ δ * ((M : ℝ) + (N : ℝ) ^ p) := by
  let Y := (2 * (M : ℝ) * N) ^ δ
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hY : 1 ≤ Y := Real.one_le_rpow (by
    have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith) hδ
  have hlo : C * Y * max 1 ((N : ℝ) ^ p / M) ≤ quadraticDilationCutoff C δ p M N := Nat.le_ceil _
  have hhi : (quadraticDilationCutoff C δ p M N : ℝ) ≤
      C * Y * max 1 ((N : ℝ) ^ p / M) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hCY : 1 ≤ C * Y := one_le_mul_of_one_le_of_one_le hC hY
  have hmax : max 1 ((N : ℝ) ^ p / M) * M = max (M : ℝ) ((N : ℝ) ^ p) := by
    rw [max_mul_of_nonneg _ _ hMR.le, one_mul, div_mul_cancel₀ _ hMR.ne']
  refine ⟨?_, ?_, ?_⟩
  · exact (le_mul_of_one_le_right (by positivity) (le_max_left _ _)).trans hlo
  · have hh := mul_le_mul_of_nonneg_right hlo hMR.le
    rw [Nat.cast_mul]
    calc
      _ ≤ max (M : ℝ) ((N : ℝ) ^ p) := le_max_right _ _
      _ ≤ C * Y * max (M : ℝ) ((N : ℝ) ^ p) := le_mul_of_one_le_left (by positivity) hCY
      _ ≤ _ := by simpa only [mul_assoc, hmax] using hh
  · have hh := mul_le_mul_of_nonneg_right hhi hMR.le
    have hm : (M : ℝ) ≤ Y * ((M : ℝ) + (N : ℝ) ^ p) := by nlinarith [Real.rpow_pos_of_pos hNR p]
    have hmaxsum : max (M : ℝ) ((N : ℝ) ^ p) ≤ (M : ℝ) + (N : ℝ) ^ p :=
      max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left hMR.le)
    rw [Nat.cast_mul]
    calc
      _ ≤ C * Y * max (M : ℝ) ((N : ℝ) ^ p) + M := by
        simpa only [add_mul, one_mul, mul_assoc, hmax] using hh
      _ ≤ C * Y * ((M : ℝ) + (N : ℝ) ^ p) + Y * ((M : ℝ) + (N : ℝ) ^ p) := by gcongr
      _ = _ := by dsimp [Y]; ring

end Ostmann

end OAI
