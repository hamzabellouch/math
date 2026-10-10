import Mathlib

namespace OAI

                                  
section

/-! A thresholded geometric scale sum with no dependence on the number of
scales. Used for designated-mover errors, not a per-level additive error. -/
noncomputable section
namespace UniformKServer.SmallScales
open Finset
open scoped Classical

theorem geometric (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q) (hq1 : q<1) (n : ℕ) :
    (∑ j∈range n, R*q^j) ≤ R/(1-q) := by
  induction n generalizing R with
  | zero => simp only [sum_range_zero]; positivity
  | succ n ih =>
    rw [sum_range_succ']
    have hh := ih (R*q) (mul_nonneg hR hq)
    have he (j : ℕ) : R*q^(j+1)=(R*q)*q^j := by rw [pow_succ]; ring
    simp only [he,pow_zero,mul_one]
    have hd : 0<1-q := by linarith
    have hid : R*q/(1-q)+R=R/(1-q) := by field_simp; ring
    calc
      _ ≤ R*q/(1-q)+R := by linarith only [hh]
      _ = _ := hid

theorem small (R q a : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q) (hq1 : q<1) (ha : 0 ≤ a) (n : ℕ) :
    (∑ j∈range n, if R*q^j ≤ a then R*q^j else 0) ≤ a/(1-q) := by
  induction n generalizing R with
  | zero => simp only [sum_range_zero]; positivity
  | succ n ih =>
    by_cases hRa : R ≤ a
    · apply le_trans (sum_le_sum (fun j _ => ?_))
        ((geometric R q hR hq hq1 (n+1)).trans (div_le_div_of_nonneg_right hRa (by linarith)))
      split_ifs <;> [exact le_rfl; exact mul_nonneg hR (pow_nonneg hq j)]
    · rw [sum_range_succ']
      have he (j : ℕ) : R*q^(j+1)=(R*q)*q^j := by rw [pow_succ]; ring
      simp only [he,pow_zero,mul_one,ite_eq_right hRa,add_zero]
      exact ih (R*q) (mul_nonneg hR hq)

theorem small_strict (R q a : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q) (hq1 : q<1) (ha : 0 ≤ a) (n : ℕ) :
    (∑ j∈range n, if R*q^j<a then R*q^j else 0) ≤ a/(1-q) := by
  apply le_trans (sum_le_sum (fun j _ => ?_)) (small R q a hR hq hq1 ha n)
  by_cases hj : R*q^j<a
  · simp only [ite_eq_left hj,ite_eq_left hj.le,le_refl]
  · simp only [ite_eq_right hj]
    split_ifs <;> [exact mul_nonneg hR (pow_nonneg hq j); exact le_rfl]

end UniformKServer.SmallScales

end


end

end OAI
