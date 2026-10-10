import Mathlib
import OAI.Combinatorics.KMedian.Analysis.AnalyticEnvelopes
import OAI.Combinatorics.KMedian.Analysis.ScalarTransfer

namespace OAI

section
section
namespace MetricKMedian.Certificates

open Analytic

private theorem T1_compat (X : ℝ) : ScalarTransfer.T1 (p X) (1-X) = T1 X := by
  unfold ScalarTransfer.T1 T1
  ring
private theorem T2_compat (X : ℝ) : ScalarTransfer.T2 (p X) (1-X) = T2 X := by
  unfold ScalarTransfer.T2 T2
  ring
private theorem Q0_compat (s : Bool) (W X : ℝ) :
    ScalarTransfer.Q0 (p X) (v X) (k X) W s = Q0 s W X := rfl
private theorem Q1_compat (s : Bool) (X : ℝ) :
    ScalarTransfer.Q1 (p X) (v X) (k X) (1-X) s = Q1 s X := rfl
private theorem Y_compat (s : Bool) (X : ℝ) :
    ScalarTransfer.Y (p X) (k X) (1-X) s = Y s X := rfl
private theorem Yprime_compat (X : ℝ) :
    ScalarTransfer.Yprime (p X) (k X) (1-X) = Yprime X := by
  unfold ScalarTransfer.Yprime Yprime N c bit
  norm_num

private theorem p_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    0 ≤ p (1-x) ∧ p (1-x) ≤ 1/2 := by
  have hlo := p_lower (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  have hhi := p_upper (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  constructor <;> linarith

private theorem T1_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    |T1 (1-x)-ScalarTransfer.T1 (P x) x| ≤ 5*(3/400000) := by
  have hb := p_bounds hx0 hx
  have he := ScalarTransfer.T1_error hb.1 hb.2 (P_nonneg x) (P_le_half hx0)
    hx0 hx (p_approximation hx0 hx)
  have hid : ScalarTransfer.T1 (p (1-x)) x = T1 (1-x) := by
    simpa only [sub_sub_cancel] using T1_compat (1-x)
  rwa [hid] at he

private theorem T2_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    |T2 (1-x)-ScalarTransfer.T2 (P x) x| ≤ 6*(3/400000) := by
  have hb := p_bounds hx0 hx
  have he := ScalarTransfer.T2_error hb.1 hb.2 (P_nonneg x) (P_le_half hx0)
    hx0 hx (p_approximation hx0 hx)
  have hid : ScalarTransfer.T2 (p (1-x)) x = T2 (1-x) := by
    simpa only [sub_sub_cancel] using T2_compat (1-x)
  rwa [hid] at he

private theorem Q0_error_actual {x W : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hW0 : 0 ≤ W) (hW : W ≤ 1) (s : Bool) :
    |Q0 s W (1-x)-ScalarTransfer.Q0 (P x) (A x) (k (1-x)) W s| ≤ 6*(3/400000) := by
  have he := ScalarTransfer.Q0_error (k := k (1-x)) hW0 hW (p_approximation hx0 hx)
    (show |v (1-x)-A x| ≤ 2*(3/400000) by convert a_approximation hx0 hx using 1; norm_num) s
  rwa [Q0_compat] at he

private theorem Q1_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    |Q1 s (1-x)-ScalarTransfer.Q1 (P x) (A x) (k (1-x)) x s| ≤ 8*(3/400000) := by
  have hb := p_bounds hx0 hx
  have he := ScalarTransfer.Q1_error (k := k (1-x)) hb.1 hb.2 (P_nonneg x) (P_le_half hx0)
    hx0 hx (p_approximation hx0 hx)
    (show |v (1-x)-A x| ≤ 2*(3/400000) by convert a_approximation hx0 hx using 1; norm_num) s
  have hid : ScalarTransfer.Q1 (p (1-x)) (v (1-x)) (k (1-x)) x s = Q1 s (1-x) := by
    simpa only [sub_sub_cancel] using Q1_compat s (1-x)
  rwa [hid] at he

private theorem Y_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    |Y s (1-x)-ScalarTransfer.Y (P x) (k (1-x)) x s| ≤ 3*(3/400000) := by
  have he := ScalarTransfer.Y_error (k := k (1-x)) hx0 hx (p_approximation hx0 hx) s
  have hid : ScalarTransfer.Y (p (1-x)) (k (1-x)) x s = Y s (1-x) := by
    simpa only [sub_sub_cancel] using Y_compat s (1-x)
  rwa [hid] at he

private theorem Yprime_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    |Yprime (1-x)-ScalarTransfer.Yprime (P x) (k (1-x)) x| ≤ 2*(3/400000) := by
  have he := ScalarTransfer.Yprime_error (k := k (1-x)) hx0 hx (p_approximation hx0 hx)
  have hid : ScalarTransfer.Yprime (p (1-x)) (k (1-x)) x = Yprime (1-x) := by
    simpa only [sub_sub_cancel] using Yprime_compat (1-x)
  rwa [hid] at he

theorem T1_actual_pos {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    0 < ScalarTransfer.T1 (P x) x := by
  have he := (abs_le.mp (T1_error_actual hx0 hx)).2
  have hc := T1_lower (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  linarith

theorem T2_actual_pos {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    0 < ScalarTransfer.T2 (P x) x := by
  have he := (abs_le.mp (T2_error_actual hx0 hx)).2
  have hc := T2_lower (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  linarith

theorem Q1_actual_pos {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    0 < ScalarTransfer.Q1 (P x) (A x) (k (1-x)) x s := by
  have he := (abs_le.mp (Q1_error_actual hx0 hx s)).2
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  cases s
  · have hc := Q10_lower hX0 hX
    linarith
  · have hc := Q11_lower hX0 hX
    linarith

theorem Q0_actual_pos {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    0 < ScalarTransfer.Q0 (P x) (A x) (k (1-x))
      (if s then ScalarTransfer.uZero s else min (1-x) (ScalarTransfer.uZero s)) s := by
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  cases s
  · by_cases hcut : 1-x ≤ 65/226
    · have he := (abs_le.mp (Q0_error_actual hx0 hx hX0 hX false)).2
      have hc := Q0X0_lower hX0 hcut
      norm_num [ScalarTransfer.uZero, ScalarTransfer.hh, ScalarTransfer.d, min_eq_left hcut]
      linarith
    · have hulo : (0:ℝ) ≤ 65/226 := by norm_num
      have huhi : (65/226:ℝ) ≤ 1 := by norm_num
      have he := (abs_le.mp (Q0_error_actual hx0 hx hulo huhi false)).2
      have hc := Q0u0_lower (le_of_not_ge hcut) hX
      norm_num [ScalarTransfer.uZero, ScalarTransfer.hh, ScalarTransfer.d,
        min_eq_right (le_of_not_ge hcut)]
      norm_num [uZero, hh, d] at hc
      linarith
  · have hulo : (0:ℝ) ≤ 5/22 := by norm_num
    have huhi : (5/22:ℝ) ≤ 1 := by norm_num
    have he := (abs_le.mp (Q0_error_actual hx0 hx hulo huhi true)).2
    have hc := Q0u1_lower hX0 hX
    norm_num [ScalarTransfer.uZero, ScalarTransfer.hh, ScalarTransfer.d]
    norm_num [uZero, hh, d] at hc
    linarith

theorem Y_actual_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool)
    (hside : s = true ∨ 1-x ≥ 1/2) :
    h (1-x) ≤ ScalarTransfer.Y (P x) (k (1-x)) x s ∧
      1/4 ≤ ScalarTransfer.Y (P x) (k (1-x)) x s := by
  have he := (abs_le.mp (Y_error_actual hx0 hx s)).2
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  cases s
  · have hrange : 1/2 ≤ 1-x := by simpa using hside
    have hc := Yh0_lower hrange hX
    have hc' := Yquarter0_lower hrange hX
    constructor <;> linarith
  · have hc := Yh1_lower hX0 hX
    have hc' := Yquarter1_lower hX0 hX
    constructor <;> linarith

theorem Yprime_actual_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hside : 1-x ≤ 1/2) :
    h (1-x) ≤ ScalarTransfer.Yprime (P x) (k (1-x)) x+(13/25)*k (1-x) ∧
      1/4 ≤ ScalarTransfer.Yprime (P x) (k (1-x)) x := by
  have he := (abs_le.mp (Yprime_error_actual hx0 hx)).2
  have hX0 := sub_nonneg.mpr hx
  have hc := Yph0_lower hX0 hside
  have hc' := Ypquarter0_lower hX0 hside
  constructor <;> linarith

end MetricKMedian.Certificates


end
end

end OAI
