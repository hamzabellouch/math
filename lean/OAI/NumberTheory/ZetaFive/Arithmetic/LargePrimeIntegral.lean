import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OAI.NumberTheory.ZetaFive.Arithmetic.LargePrimeTable

namespace OAI

namespace Zeta5.Workers.W20
open MeasureTheory Set

private theorem affine_integral (a b slope intercept : ℝ) :
    (∫ x in a..b, slope * x + intercept) =
      slope * (b ^ 2 - a ^ 2) / 2 + intercept * (b - a) := by
  have hlinear : IntervalIntegrable (fun x : ℝ => slope * x) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  have hconstant : IntervalIntegrable (fun _ : ℝ => intercept) volume a b :=
    continuous_const.intervalIntegrable a b
  rw [intervalIntegral.integral_add hlinear hconstant,
    intervalIntegral.integral_const_mul slope (fun x : ℝ => x), integral_id,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  calc
    _ = (b - a) * (slope * ((a + b) / 2) + intercept) := by ring
    _ = slope * (b ^ 2 - a ^ 2) / 2 + intercept * (b - a) := by ring

private theorem affine_piece {a b slope intercept : ℝ}
    (hab : a ≤ b)
    (hpiece : ∀ x, a < x → x < b → largePrimeLimit x = slope * x + intercept) :
    IntervalIntegrable largePrimeLimit volume a b ∧
      (∫ x in a..b, largePrimeLimit x) =
        slope * (b ^ 2 - a ^ 2) / 2 + intercept * (b - a) := by
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
    have hi : IntervalIntegrable (fun x : ℝ => slope * x + intercept) volume a b :=
      ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable a b
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hi
    exact hi.congr_fun (fun x hx => (hpiece x hx.1 hx.2).symm) measurableSet_Ioo
  · rw [intervalIntegral.integral_congr_Ioo_of_le hab (fun x hx => hpiece x hx.1 hx.2),
      affine_integral]

theorem integral_piece_01 :
    IntervalIntegrable largePrimeLimit volume (9) (46 / 5) ∧
      (∫ x in (9)..(46 / 5), largePrimeLimit x) = -274 / 25 := by
  have h := affine_piece (a := (9)) (b := (46 / 5)) (slope := 2)
    (intercept := (-73)) (by norm_num)
    (fun x ha hb => by simpa only [sub_eq_add_neg] using piece_01 ha hb)
  norm_num at h ⊢
  exact h

theorem integral_piece_02 :
    IntervalIntegrable largePrimeLimit volume (46 / 5) (19 / 2) ∧
      (∫ x in (46 / 5)..(19 / 2), largePrimeLimit x) = -3213 / 200 := by
  have h := affine_piece (a := (46 / 5)) (b := (19 / 2)) (slope := 7)
    (intercept := (-119)) (by norm_num)
    (fun x ha hb => by simpa only [sub_eq_add_neg] using piece_02 ha hb)
  norm_num at h ⊢
  exact h

theorem integral_piece_03 :
    IntervalIntegrable largePrimeLimit volume (19 / 2) (10) ∧
      (∫ x in (19 / 2)..(10), largePrimeLimit x) = -195 / 8 := by
  have h := affine_piece (a := (19 / 2)) (b := (10)) (slope := 15)
    (intercept := (-195)) (by norm_num)
    (fun x ha hb => by simpa only [sub_eq_add_neg] using piece_03 ha hb)
  norm_num at h ⊢
  exact h

theorem integral_piece_04 :
    IntervalIntegrable largePrimeLimit volume (10) (11) ∧
      (∫ x in (10)..(11), largePrimeLimit x) = -71 / 2 := by
  have h := affine_piece (a := (10)) (b := (11)) (slope := 19)
    (intercept := (-235)) (by norm_num)
    (fun x ha hb => by simpa only [sub_eq_add_neg] using piece_04 ha hb)
  norm_num at h ⊢
  exact h

theorem integral_piece_05 :
    IntervalIntegrable largePrimeLimit volume (11) (12) ∧
      (∫ x in (11)..(12), largePrimeLimit x) = -35 / 2 := by
  have h := affine_piece (a := (11)) (b := (12)) (slope := 17)
    (intercept := (-213)) (by norm_num)
    (fun x ha hb => by simpa only [sub_eq_add_neg] using piece_05 ha hb)
  norm_num at h ⊢
  exact h

theorem integral_piece_06 :
    IntervalIntegrable largePrimeLimit volume (12) (15) ∧
      (∫ x in (12)..(15), largePrimeLimit x) = 81 / 2 := by
  have h := affine_piece (a := (12)) (b := (15)) (slope := 15)
    (intercept := (-189)) (by norm_num)
    (fun x ha hb => by simpa only [sub_eq_add_neg] using piece_06 ha hb)
  norm_num at h ⊢
  exact h

theorem integral_piece_07 :
    IntervalIntegrable largePrimeLimit volume (15) (16) ∧
      (∫ x in (15)..(16), largePrimeLimit x) = 42 := by
  have h := affine_piece (a := (15)) (b := (16)) (slope := 12)
    (intercept := (-144)) (by norm_num)
    (fun x ha hb => by simpa only [sub_eq_add_neg] using piece_07 ha hb)
  norm_num at h ⊢
  exact h

theorem integral_piece_08 :
    IntervalIntegrable largePrimeLimit volume (16) (18) ∧
      (∫ x in (16)..(18), largePrimeLimit x) = 48 := by
  have h := affine_piece (a := (16)) (b := (18)) (slope := 6)
    (intercept := (-78)) (by norm_num)
    (fun x ha hb => by simpa only [sub_eq_add_neg] using piece_08 ha hb)
  norm_num at h ⊢
  exact h

theorem largePrimeLimit_integral :
    (∫ x in (9 : ℝ)..18, largePrimeLimit x) = 261 / 10 := by
  have h01 := integral_piece_01
  have h02 := integral_piece_02
  have h03 := integral_piece_03
  have h04 := integral_piece_04
  have h05 := integral_piece_05
  have h06 := integral_piece_06
  have h07 := integral_piece_07
  have h08 := integral_piece_08
  have i02 := h01.1.trans h02.1
  have i03 := i02.trans h03.1
  have i04 := i03.trans h04.1
  have i05 := i04.trans h05.1
  have i06 := i05.trans h06.1
  have i07 := i06.trans h07.1
  rw [← intervalIntegral.integral_add_adjacent_intervals i07 h08.1,
    ← intervalIntegral.integral_add_adjacent_intervals i06 h07.1,
    ← intervalIntegral.integral_add_adjacent_intervals i05 h06.1,
    ← intervalIntegral.integral_add_adjacent_intervals i04 h05.1,
    ← intervalIntegral.integral_add_adjacent_intervals i03 h04.1,
    ← intervalIntegral.integral_add_adjacent_intervals i02 h03.1,
    ← intervalIntegral.integral_add_adjacent_intervals h01.1 h02.1,
    h01.2, h02.2, h03.2, h04.2, h05.2, h06.2, h07.2, h08.2]
  norm_num

theorem largePrimeLimit_normalized_integral :
    (1 / 270 : ℝ) * (∫ x in (9 : ℝ)..18, largePrimeLimit x) = 29 / 300 := by
  rw [largePrimeLimit_integral]
  norm_num

end Zeta5.Workers.W20

end OAI
