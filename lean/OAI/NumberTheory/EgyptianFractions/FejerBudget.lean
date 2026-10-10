import Mathlib

namespace OAI
noncomputable section
namespace Problem337

/-- Rounding the inner cyclic interval leaves fixed proportional margins. -/
theorem cyclic_interval_floor_budget (δ : ℝ) (q : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hscale : 128 ≤ δ * q) :
    let d := ⌊δ * q / 8⌋₊
    1 ≤ d ∧ 7 * d < q ∧ (8 * d : ℕ) ≤ δ * q ∧
    δ / 16 ≤ (d : ℝ) / q ∧
    11 * δ / 16 ≤ ((6 * d + 1 : ℕ) : ℝ) / q ∧
    ((6 * d + 1 : ℕ) : ℝ) / q ≤ δ := by
  let d := ⌊δ * q / 8⌋₊
  change 1 ≤ d ∧ 7 * d < q ∧ (8 * d : ℕ) ≤ δ * q ∧
    δ / 16 ≤ (d : ℝ) / q ∧
    11 * δ / 16 ≤ ((6 * d + 1 : ℕ) : ℝ) / q ∧
    ((6 * d + 1 : ℕ) : ℝ) / q ≤ δ
  have hq : (0 : ℝ) < q := by
    by_contra h
    have hq0 : (q : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg q)
    rw [hq0] at hscale
    norm_num at hscale
  have hdhi : (d : ℝ) ≤ δ * q / 8 := Nat.floor_le (by positivity)
  have hdlo : δ * q / 8 < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  have hδq : δ * q ≤ (q : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hδ1 hq.le]
  have hd1 : 1 ≤ d := by exact_mod_cast (show (1 : ℝ) ≤ d by linarith)
  have hdb : 7 * d < q := by exact_mod_cast (show 7 * (d : ℝ) < q by linarith)
  refine ⟨hd1, hdb, ?_, ?_, ?_, ?_⟩
  · push_cast
    linarith
  · apply (le_div_iff₀ hq).mpr
    linarith
  · apply (le_div_iff₀ hq).mpr
    push_cast
    linarith
  · apply (div_le_iff₀ hq).mpr
    push_cast
    linarith

/-- A low-degree kernel simultaneously has small leakage and Fourier error. -/
theorem fejer_degree_floor_budget (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) :
    let h := ⌊1 / (64 * δ ^ 3)⌋₊
    1 ≤ h ∧ 1 / (128 * δ ^ 3) ≤ (h : ℝ) ∧
    (h : ℝ) ≤ 1 / (64 * δ ^ 3) ∧
    64 / ((h : ℝ) * δ) ≤ δ / 8 ∧
    2 * (h : ℝ) * δ * δ ^ 3 ≤ δ / 32 := by
  let h := ⌊1 / (64 * δ ^ 3)⌋₊
  change 1 ≤ h ∧ 1 / (128 * δ ^ 3) ≤ (h : ℝ) ∧
    (h : ℝ) ≤ 1 / (64 * δ ^ 3) ∧
    64 / ((h : ℝ) * δ) ≤ δ / 8 ∧
    2 * (h : ℝ) * δ * δ ^ 3 ≤ δ / 32
  have hcube : 0 < δ ^ 3 := by positivity
  have hcubehi : δ ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := by
    gcongr
    norm_num at *
    linarith
  have harg2 : (2 : ℝ) ≤ 1 / (64 * δ ^ 3) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * δ ^ 3)).mpr
    norm_num at hcubehi
    linarith
  have hhhi : (h : ℝ) ≤ 1 / (64 * δ ^ 3) := Nat.floor_le (by positivity)
  have hhlo : 1 / (64 * δ ^ 3) < (h : ℝ) + 1 := Nat.lt_floor_add_one _
  have hh1 : 1 ≤ h := by exact_mod_cast (show (1 : ℝ) ≤ h by linarith)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have half : 1 / (128 * δ ^ 3) = (1 / (64 * δ ^ 3)) / 2 := by ring
  have hhalf : 1 / (128 * δ ^ 3) ≤ (h : ℝ) := by rw [half]; linarith
  refine ⟨hh1, hhalf, hhhi, ?_, ?_⟩
  · calc
      64 / ((h : ℝ) * δ) ≤ 64 / ((1 / (128 * δ ^ 3)) * δ) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right hhalf hδ.le
      _ = 8192 * δ ^ 2 := by
        field_simp
        ring
      _ ≤ δ / 8 := by
        have hh := mul_le_mul_of_nonneg_right hsmall hδ.le
        nlinarith
  · calc
      2 * (h : ℝ) * δ * δ ^ 3 ≤ 2 * (1 / (64 * δ ^ 3)) * δ * δ ^ 3 := by
        gcongr
      _ = δ / 32 := by
        field_simp
        ring

/-- The chosen degree uses only the prescribed low frequencies. -/
theorem fejer_degree_frequency_bound (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) :
    ⌊1 / (64 * δ ^ 3)⌋₊ ≤ ⌊1 / δ ^ 4⌋₊ := by
  apply Nat.floor_mono
  apply one_div_le_one_div_of_le (by positivity)
  have hh := mul_le_mul_of_nonneg_right (show δ ≤ 64 by linarith)
    (show 0 ≤ δ ^ 3 by positivity)
  nlinarith

/-- The three error budgets leave at least half the target interval mass. -/
theorem fejer_localization_budget (δ mass inner error leakage : ℝ)
    (hδ : 0 ≤ δ) (hinner : 11 * δ / 16 ≤ inner)
    (herror : error ≤ δ / 32) (hleakage : leakage ≤ δ / 8)
    (hmass : inner - error - leakage ≤ mass) : δ / 2 ≤ mass := by
  linarith

end Problem337

end

end OAI
