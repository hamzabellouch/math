import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondBlockError

namespace OAI

/-! # Absorbing the polynomial block cost into the chosen Poisson truncation -/

namespace Ostmann

theorem quadratic_error_power_choice {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ A : ℕ, ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      (Real.sqrt M * (2 * N)) / ((M * N) ^ δ) ^ A ≤ 2 / (M * N) ^ P := by
  obtain ⟨A, hA⟩ := exists_nat_ge (((P : ℝ) + 1) / δ)
  refine ⟨A, ?_⟩
  intro M N hM hN
  have hMN : 1 ≤ M * N := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sub_nonneg.mpr hN)]
  have hMN₀ : 0 < M * N := zero_lt_one.trans_le hMN
  have he : (P : ℝ) + 1 ≤ δ * A := by
    have hh := (div_le_iff₀ hδ).mp hA
    nlinarith
  have hden : (M * N) ^ (P + 1) ≤ ((M * N) ^ δ) ^ A := by
    calc
      _ = (M * N) ^ ((P : ℝ) + 1) := by rw [← Real.rpow_natCast]; norm_num
      _ ≤ (M * N) ^ (δ * A) := Real.rpow_le_rpow_of_exponent_le hMN he
      _ = _ := by rw [Real.rpow_mul hMN₀.le, Real.rpow_natCast]
  have hsqrt : Real.sqrt M ≤ M := Real.sqrt_le_self_iff.mpr (Or.inr hM)
  calc
    _ ≤ (2 * (M * N)) / ((M * N) ^ δ) ^ A := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ ≤ (2 * (M * N)) / (M * N) ^ (P + 1) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hMN₀ _) hden
    _ = _ := by rw [pow_succ]; field_simp

end Ostmann

end OAI
