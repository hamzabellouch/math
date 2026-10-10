import Mathlib

namespace OAI

noncomputable section

namespace Problem340

def predictionMajorant (C B L : ℝ) (n : ℕ) : ℝ :=
  C * (L⁻¹) ^ n * (1 + B ^ (n + 1) + 2 ^ (n + 2))

theorem summable_predictionMajorant {C B L : ℝ}
    (hB : 0 ≤ B) (hBL : B < L) (hL : 2 < L) :
    Summable (predictionMajorant C B L) := by
  have hL0 : 0 < L := by linarith
  have hInv : L⁻¹ < 1 := by
    rw [inv_lt_one₀ hL0]
    linarith
  have hRatioB : B * L⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hL0]
    exact hBL
  have hRatio2 : 2 * L⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hL0]
    exact hL
  have h₀ : Summable (fun n : ℕ => (L⁻¹) ^ n) :=
    summable_geometric_of_lt_one (inv_nonneg.mpr hL0.le) hInv
  have h₁ : Summable (fun n : ℕ => (B * L⁻¹) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg hB (inv_nonneg.mpr hL0.le)) hRatioB
  have h₂ : Summable (fun n : ℕ => (2 * L⁻¹) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hRatio2
  have hs := ((h₀.add (h₁.mul_left B)).add (h₂.mul_left 4)).mul_left C
  apply hs.congr
  intro n
  simp only [predictionMajorant, mul_pow, pow_add, pow_one, pow_two]
  ring

theorem contDiff_one_tsum_of_norm_add_fderiv_le
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ι → E → F} {u : ι → ℝ}
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hu : Summable u)
    (hb : ∀ i x, ‖f i x‖ + ‖fderiv ℝ (f i) x‖ ≤ u i) :
    ContDiff ℝ 1 (fun x => ∑' i, f i x) := by
  apply contDiff_tsum hf (v := fun _ => u)
  · intro k hk
    exact hu
  · intro k i x hk
    have hk' : k ≤ 1 := by exact_mod_cast hk
    interval_cases k
    · simpa only [norm_iteratedFDeriv_zero] using
        (le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hb i x))
    · simpa only [norm_iteratedFDeriv_one] using
        (le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hb i x))

theorem contDiff_one_tsum_prediction
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} {C B L : ℝ}
    (hB : 0 ≤ B) (hBL : B < L) (hL : 2 < L)
    (hf : ∀ n, ContDiff ℝ 1 (f n))
    (hb : ∀ n x, ‖f n x‖ + ‖fderiv ℝ (f n) x‖ ≤ predictionMajorant C B L n) :
    ContDiff ℝ 1 (fun x => ∑' n, f n x) :=
  contDiff_one_tsum_of_norm_add_fderiv_le hf
    (summable_predictionMajorant hB hBL hL) hb

end Problem340

end

end OAI
