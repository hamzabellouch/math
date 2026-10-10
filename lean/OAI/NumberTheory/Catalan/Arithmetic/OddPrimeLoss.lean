import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI


noncomputable section
open MeasureTheory Set
open scoped Interval

namespace InternalCatalan

def oddPrimeLoss (x : ℝ) : ℝ :=
  96 - 2 * max (x - 25) 0 + 2 * max (x - 29) 0 -
    2 * max (x - 65 / 2) 0 - 2 * max (x - 69 / 2) 0 +
    max (x - 40) 0 + max (x - 58) 0 + max (x - 59) 0 + max (x - 65) 0

theorem continuous_oddPrimeLoss : Continuous oddPrimeLoss := by
  unfold oddPrimeLoss
  fun_prop

theorem oddPrimeLoss_of_le_25 (x : ℝ) (hhi : x ≤ 25) :
    oddPrimeLoss x = 96 := by
  simp only [oddPrimeLoss,
    max_eq_right (show x - 25 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 29 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 69 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_25_29 (x : ℝ) (hlo : 25 ≤ x) (hhi : x ≤ 29) :
    oddPrimeLoss x = 146 - 2 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_right (show x - 29 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 69 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_29_65div2 (x : ℝ) (hlo : 29 ≤ x) (hhi : x ≤ 65 / 2) :
    oddPrimeLoss x = 88 := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_right (show x - 65 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 69 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_65div2_69div2 (x : ℝ) (hlo : 65 / 2 ≤ x) (hhi : x ≤ 69 / 2) :
    oddPrimeLoss x = 153 - 2 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_right (show x - 69 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_69div2_40 (x : ℝ) (hlo : 69 / 2 ≤ x) (hhi : x ≤ 40) :
    oddPrimeLoss x = 222 - 4 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_40_58 (x : ℝ) (hlo : 40 ≤ x) (hhi : x ≤ 58) :
    oddPrimeLoss x = 182 - 3 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 40 by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_58_59 (x : ℝ) (hlo : 58 ≤ x) (hhi : x ≤ 59) :
    oddPrimeLoss x = 124 - 2 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 40 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 58 by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_59_65 (x : ℝ) (hlo : 59 ≤ x) (hhi : x ≤ 65) :
    oddPrimeLoss x = 65 - x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 40 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 58 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 59 by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_of_ge_65 (x : ℝ) (hlo : 65 ≤ x) :
    oddPrimeLoss x = 0 := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 40 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 58 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 59 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 by linarith)]
  ring

theorem oddPrimeLoss_mem_Icc (x : ℝ) : oddPrimeLoss x ∈ Icc (0 : ℝ) 96 := by
  by_cases h0 : x ≤ 25
  · rw [oddPrimeLoss_of_le_25 x h0]
    constructor <;> linarith
  by_cases h1 : x ≤ 29
  · rw [oddPrimeLoss_25_29 x (by linarith) h1]
    constructor <;> linarith
  by_cases h2 : x ≤ 65 / 2
  · rw [oddPrimeLoss_29_65div2 x (by linarith) h2]
    constructor <;> linarith
  by_cases h3 : x ≤ 69 / 2
  · rw [oddPrimeLoss_65div2_69div2 x (by linarith) h3]
    constructor <;> linarith
  by_cases h4 : x ≤ 40
  · rw [oddPrimeLoss_69div2_40 x (by linarith) h4]
    constructor <;> linarith
  by_cases h5 : x ≤ 58
  · rw [oddPrimeLoss_40_58 x (by linarith) h5]
    constructor <;> linarith
  by_cases h6 : x ≤ 59
  · rw [oddPrimeLoss_58_59 x (by linarith) h6]
    constructor <;> linarith
  by_cases h7 : x ≤ 65
  · rw [oddPrimeLoss_59_65 x (by linarith) h7]
    constructor <;> linarith
  rw [oddPrimeLoss_of_ge_65 x (by linarith)]
  constructor <;> norm_num

theorem oddPrimeLoss_nonneg (x : ℝ) : 0 ≤ oddPrimeLoss x :=
  (oddPrimeLoss_mem_Icc x).1

theorem oddPrimeLoss_le (x : ℝ) : oddPrimeLoss x ≤ 96 :=
  (oddPrimeLoss_mem_Icc x).2

private theorem loss_integral_affine (a b c m : ℝ) :
    (∫ x in a..b, c - m * x) = c * (b - a) - m * ((b ^ 2 - a ^ 2) / 2) := by
  rw [intervalIntegral.integral_sub
    (f := fun _ : ℝ => c) (g := fun x : ℝ => m * x)
    (continuous_const.intervalIntegrable a b)
    ((continuous_const.mul continuous_id).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul m (fun x : ℝ => x)]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

theorem integral_oddPrimeLoss_0_25 :
    (∫ x in (0 : ℝ)..(25), oddPrimeLoss x) = 2400 := by
  calc
    (∫ x in (0 : ℝ)..(25), oddPrimeLoss x) =
        ∫ x in (0 : ℝ)..(25), 96 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_of_le_25 x hx.2
    _ = 2400 := by norm_num [intervalIntegral.integral_const]

theorem integral_oddPrimeLoss_25_29 :
    (∫ x in (25 : ℝ)..(29), oddPrimeLoss x) = 368 := by
  calc
    (∫ x in (25 : ℝ)..(29), oddPrimeLoss x) =
        ∫ x in (25 : ℝ)..(29), 146 - 2 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_25_29 x hx.1 hx.2
    _ = 368 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_29_65div2 :
    (∫ x in (29 : ℝ)..(65 / 2), oddPrimeLoss x) = 308 := by
  calc
    (∫ x in (29 : ℝ)..(65 / 2), oddPrimeLoss x) =
        ∫ x in (29 : ℝ)..(65 / 2), 88 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_29_65div2 x hx.1 hx.2
    _ = 308 := by norm_num [intervalIntegral.integral_const]

theorem integral_oddPrimeLoss_65div2_69div2 :
    (∫ x in (65 / 2 : ℝ)..(69 / 2), oddPrimeLoss x) = 172 := by
  calc
    (∫ x in (65 / 2 : ℝ)..(69 / 2), oddPrimeLoss x) =
        ∫ x in (65 / 2 : ℝ)..(69 / 2), 153 - 2 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_65div2_69div2 x hx.1 hx.2
    _ = 172 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_69div2_40 :
    (∫ x in (69 / 2 : ℝ)..(40), oddPrimeLoss x) = 803 / 2 := by
  calc
    (∫ x in (69 / 2 : ℝ)..(40), oddPrimeLoss x) =
        ∫ x in (69 / 2 : ℝ)..(40), 222 - 4 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_69div2_40 x hx.1 hx.2
    _ = 803 / 2 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_40_58 :
    (∫ x in (40 : ℝ)..(58), oddPrimeLoss x) = 630 := by
  calc
    (∫ x in (40 : ℝ)..(58), oddPrimeLoss x) =
        ∫ x in (40 : ℝ)..(58), 182 - 3 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_40_58 x hx.1 hx.2
    _ = 630 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_58_59 :
    (∫ x in (58 : ℝ)..(59), oddPrimeLoss x) = 7 := by
  calc
    (∫ x in (58 : ℝ)..(59), oddPrimeLoss x) =
        ∫ x in (58 : ℝ)..(59), 124 - 2 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_58_59 x hx.1 hx.2
    _ = 7 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_59_65 :
    (∫ x in (59 : ℝ)..(65), oddPrimeLoss x) = 18 := by
  calc
    (∫ x in (59 : ℝ)..(65), oddPrimeLoss x) =
        ∫ x in (59 : ℝ)..(65), 65 - x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_59_65 x hx.1 hx.2
    _ = 18 := by
      simpa only [one_mul] using
        (show (∫ x in (59 : ℝ)..65, 65 - 1 * x) = 18 by
          rw [loss_integral_affine]; norm_num)

theorem integral_oddPrimeLoss :
    (∫ x in (0 : ℝ)..65, oddPrimeLoss x) = 8609 / 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (0) (25))
    (continuous_oddPrimeLoss.intervalIntegrable (25) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (25) (29))
    (continuous_oddPrimeLoss.intervalIntegrable (29) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (29) (65 / 2))
    (continuous_oddPrimeLoss.intervalIntegrable (65 / 2) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (65 / 2) (69 / 2))
    (continuous_oddPrimeLoss.intervalIntegrable (69 / 2) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (69 / 2) (40))
    (continuous_oddPrimeLoss.intervalIntegrable (40) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (40) (58))
    (continuous_oddPrimeLoss.intervalIntegrable (58) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (58) (59))
    (continuous_oddPrimeLoss.intervalIntegrable (59) 65)]
  rw [integral_oddPrimeLoss_0_25,
    integral_oddPrimeLoss_25_29,
    integral_oddPrimeLoss_29_65div2,
    integral_oddPrimeLoss_65div2_69div2,
    integral_oddPrimeLoss_69div2_40,
    integral_oddPrimeLoss_40_58,
    integral_oddPrimeLoss_58_59,
    integral_oddPrimeLoss_59_65]
  norm_num

theorem integral_oddPrimeLoss_25_65 :
    (∫ x in (25 : ℝ)..65, oddPrimeLoss x) = 3809 / 2 := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous_oddPrimeLoss.intervalIntegrable 0 25)
    (continuous_oddPrimeLoss.intervalIntegrable 25 65)
  rw [integral_oddPrimeLoss_0_25, integral_oddPrimeLoss] at h
  linarith

end InternalCatalan

end

end OAI
