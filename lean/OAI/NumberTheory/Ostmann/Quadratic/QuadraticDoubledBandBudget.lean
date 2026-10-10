import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGrowthBandBalance
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionWeightBalance

namespace OAI

/-! # The coefficient interval [N,2N] and the original correction normalizers -/

namespace Ostmann

theorem quadratic_first_doubled_band_balance {M N B D F Y E : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hD : 1 ≤ D)
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E) :
    min (M / N) (Real.sqrt M / (Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y (2 * N) D E ≤
      16 * F * (2 * M + Real.sqrt (2 * M) / Real.sqrt B * Y) * E := by
  have heq : M / N = (2 * M) / (2 * N) := by ring
  have hsq : Real.sqrt M ≤ Real.sqrt (2 * M) := Real.sqrt_le_sqrt (by linarith)
  have hmin : min (M / N) (Real.sqrt M / (Real.sqrt B * D)) ≤
      min ((2 * M) / (2 * N)) (Real.sqrt (2 * M) / (Real.sqrt B * D)) := by
    rw [heq]
    exact min_le_min le_rfl (div_le_div_of_nonneg_right hsq (by positivity))
  exact (mul_le_mul_of_nonneg_right hmin
    (quadratic_growth_band_budget_nonneg hF hY (by positivity) (by positivity) hE)).trans
    (quadratic_first_growth_band_balance (by positivity) (by positivity) hB hD hF hY hE)

theorem quadratic_first_low_budget {M N J F Y E : ℝ} {e B D : ℕ}
    (hM : 0 < M) (hN : 0 < N) (he : 0 < e) (hB : 0 < B) (hD : 0 < D)
    (hJ : 1 ≤ J) (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hcut : (D : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J) :
    (M / ((e : ℝ) * N)) * quadraticGrowthBandBudget F Y (2 * N) D E ≤
      32 * J * F * (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * Y) * E := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hα : M / ((e : ℝ) * N) = (M / e) / N := by ring
  have hβ : Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) =
      Real.sqrt (M / e) / (Real.sqrt B * D) := by
    rw [Real.sqrt_div hM.le]
    ring
  have hw := quadratic_low_weight_balance hM hN he hB hD hJ hcut
  rw [hα, hβ] at hw
  have hb := quadratic_first_doubled_band_balance (div_pos hM heR) hN hBR hDR hF hY hE
  have ht : 0 ≤ quadraticGrowthBandBudget F Y (2 * N) D E :=
    quadratic_growth_band_budget_nonneg hF hY (by positivity) (by positivity) hE
  rw [hα]
  calc
    _ ≤ (2 * J * min ((M / e) / N) (Real.sqrt (M / e) / (Real.sqrt B * D))) *
        quadraticGrowthBandBudget F Y (2 * N) D E := mul_le_mul_of_nonneg_right hw ht
    _ = (2 * J) * (min ((M / e) / N) (Real.sqrt (M / e) / (Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y (2 * N) D E) := by ring
    _ ≤ (2 * J) * (16 * F * (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * Y) * E) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem quadratic_first_high_budget {M N J F Y E : ℝ} {e B D : ℕ}
    (hM : 0 < M) (hN : 0 < N) (he : 0 < e) (hB : 0 < B) (hD : 0 < D)
    (hJ : 1 ≤ J) (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hcut : quadraticCorrectionBase M N e B / (8 * J) ≤ (D : ℝ)) :
    (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y (2 * N) D E ≤
      128 * J * F * (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * Y) * E := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hα : M / ((e : ℝ) * N) = (M / e) / N := by ring
  have hβ : Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) =
      Real.sqrt (M / e) / (Real.sqrt B * D) := by
    rw [Real.sqrt_div hM.le]
    ring
  have hw := quadratic_high_weight_balance hM hN he hB hD hJ hcut
  rw [hα, hβ] at hw
  have hb := quadratic_first_doubled_band_balance (div_pos hM heR) hN hBR hDR hF hY hE
  have ht : 0 ≤ quadraticGrowthBandBudget F Y (2 * N) D E :=
    quadratic_growth_band_budget_nonneg hF hY (by positivity) (by positivity) hE
  rw [hβ]
  calc
    _ ≤ (8 * J * min ((M / e) / N) (Real.sqrt (M / e) / (Real.sqrt B * D))) *
        quadraticGrowthBandBudget F Y (2 * N) D E := mul_le_mul_of_nonneg_right hw ht
    _ = (8 * J) * (min ((M / e) / N) (Real.sqrt (M / e) / (Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y (2 * N) D E) := by ring
    _ ≤ (8 * J) * (16 * F * (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * Y) * E) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
