import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGrowthMatrixCost

namespace OAI

/-! # The common band budget has the required low/high recursive size -/

namespace Ostmann

noncomputable def quadraticGrowthBandBudget (F Y N D E : ℝ) : ℝ :=
  8 * F * Real.sqrt D * (Y + Real.sqrt (Y * N) + N / Real.sqrt D) * E

theorem quadratic_growth_band_budget_nonneg {F Y N D E : ℝ}
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hN : 0 ≤ N) (_hD : 0 ≤ D) (hE : 0 ≤ E) :
    0 ≤ quadraticGrowthBandBudget F Y N D E := by
  unfold quadraticGrowthBandBudget
  positivity

/-- The minimum comes from the two outer corrections, with the actual
normalizations M/N and sqrt(M)/(sqrt(B)D). -/
theorem quadratic_first_growth_band_balance {M N B D F Y E : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hD : 1 ≤ D)
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E) :
    min (M / N) (Real.sqrt M / (Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y N D E ≤
      16 * F * (M + Real.sqrt M / Real.sqrt B * Y) * E := by
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hsM₀ : Real.sqrt M ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
  have hid : (M / N) * (N / (Real.sqrt M * Real.sqrt B * D)) =
      Real.sqrt M / (Real.sqrt B * D) := by
    field_simp
    nlinarith only [Real.sq_sqrt hM.le]
  have hmin : min (M / N) (Real.sqrt M / (Real.sqrt B * D)) =
      (M / N) * min 1 (N / (Real.sqrt M * Real.sqrt B * D)) := by
    rw [mul_min_of_nonneg _ _ (div_nonneg hM.le hN.le), mul_one, hid]
  have hb := quadratic_comparison_envelope hM hN hB hD hY
  rw [hmin]
  unfold quadraticGrowthBandBudget
  calc
    _ = (8 * F * E) *
        ((M / N * Real.sqrt D * min 1 (N / (Real.sqrt M * Real.sqrt B * D))) *
          (Y + Real.sqrt (Y * N) + N / Real.sqrt D)) := by ring
    _ ≤ (8 * F * E) * (2 * (M + Real.sqrt M / Real.sqrt B * Y)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem quadratic_second_growth_band_balance {M N B D F Y E A : ℝ}
    (hM : 0 < M) (hN : 0 ≤ N) (hB : 0 < B) (hD : 1 ≤ D)
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / (Real.sqrt B * D) ≤ A) :
    (Real.sqrt M / (Real.sqrt B * D)) * quadraticGrowthBandBudget F Y N D E ≤
      16 * F * (Real.sqrt M / Real.sqrt B * Y + A * N) * E := by
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hsD₀ : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD₀).ne'
  have hid : Real.sqrt M / (Real.sqrt B * D) * Real.sqrt D =
      Real.sqrt M / (Real.sqrt B * Real.sqrt D) := by
    field_simp
    nlinarith only [Real.sq_sqrt hD₀.le]
  have hb := quadratic_small_kernel_envelope hM hN hB hD hY hA hcut
  unfold quadraticGrowthBandBudget
  calc
    _ = (8 * F * E) * ((Real.sqrt M / (Real.sqrt B * D) * Real.sqrt D) *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D)) := by ring
    _ = (8 * F * E) * ((Real.sqrt M / (Real.sqrt B * Real.sqrt D)) *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D)) := by rw [hid]
    _ ≤ (8 * F * E) * (2 * (Real.sqrt M / Real.sqrt B * Y + A * N)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
