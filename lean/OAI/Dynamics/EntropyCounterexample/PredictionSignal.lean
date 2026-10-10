import Mathlib

namespace OAI

noncomputable section

namespace Problem340

theorem prediction_input_eq_delayed_signal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L α βj : ℝ) (B : ℕ → ℝ) (Φ : ℕ → E)
    (i j : ℕ) (hij : i < j)
    (hhit : ∀ m : ℕ, 1 ≤ m → B m = if m = j - i then βj else 0) :
    (α / 10) • (∑' n : ℕ, ((L⁻¹) ^ n * B (n + 1)) • Φ (n + 1)) =
      L ^ (1 + (i : ℤ) - (j : ℤ)) • ((α * βj / 10) • Φ (j - i)) := by
  classical
  have hd : 1 ≤ j - i := by omega
  have hindex : j - i - 1 + 1 = j - i := by omega
  have hsum : (∑' n : ℕ, ((L⁻¹) ^ n * B (n + 1)) • Φ (n + 1)) =
      ((L⁻¹) ^ (j - i - 1) * βj) • Φ (j - i) := by
    rw [tsum_eq_single (j - i - 1)]
    · rw [hindex, hhit (j - i) hd, ite_eq_left rfl]
    · intro n hn
      have hne : n + 1 ≠ j - i := by omega
      rw [hhit (n + 1) (by omega), ite_eq_right hne]
      simp
  have hz : -(↑(j - i - 1) : ℤ) = 1 + (i : ℤ) - (j : ℤ) := by omega
  have hpow : (L⁻¹) ^ (j - i - 1) = L ^ (1 + (i : ℤ) - (j : ℤ)) := by
    rw [← hz, zpow_neg, zpow_natCast, inv_pow]
  rw [hsum, hpow, smul_smul, smul_smul]
  congr 1
  ring

theorem scheduled_signal_norm_le_tenth
    {α β χ : ℝ} (hα : α ∈ Set.Icc 0 1) (hβ : β ∈ Set.Icc 0 1)
    (hχ : χ ∈ Set.Icc 0 1) {θ : ℂ} (hθ : ‖θ‖ = 1) (k : ℕ) :
    ‖((β / 10 * α * χ : ℝ) : ℂ) * θ ^ k‖ ≤ (1 / 10 : ℝ) := by
  rw [norm_mul, norm_pow, hθ, one_pow, mul_one, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (mul_nonneg (div_nonneg hβ.1 (by norm_num)) hα.1) hχ.1)]
  have hβα : β * α ≤ 1 := by
    simpa using mul_le_mul hβ.2 hα.2 hα.1 (show (0 : ℝ) ≤ 1 by norm_num)
  have hβα0 : 0 ≤ β * α := mul_nonneg hβ.1 hα.1
  have hprod : β * α * χ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hχ.2 hβα0
    nlinarith
  nlinarith

theorem sum_norm_signals_le_half
    {ι E : Type*} [NormedAddCommGroup E]
    (I : Finset ι) (c : ι → E) (hcard : I.card ≤ 5)
    (hc : ∀ i ∈ I, ‖c i‖ ≤ (1 / 10 : ℝ)) :
    ∑ i ∈ I, ‖c i‖ ≤ (1 / 2 : ℝ) := by
  have hsum := Finset.sum_le_sum hc
  have hcard' : (I.card : ℝ) ≤ 5 := by exact_mod_cast hcard
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  exact hsum.trans (by linarith)

end Problem340

end

end OAI
