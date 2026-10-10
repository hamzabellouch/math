import Mathlib

namespace OAI

namespace Ostmann.FiniteField

theorem nested_sqrt_prime_bound (x : ℝ) (hx : 0<x) :
    Real.sqrt (Real.sqrt (3/x))≤2*x^(-(1/4:ℝ)) := by
  have hs : Real.sqrt (Real.sqrt (3:ℝ))≤2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · apply Real.sqrt_le_iff.mpr
      norm_num
  have hroot : Real.sqrt (Real.sqrt x)=x^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hx.le]
    norm_num
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤3),Real.sqrt_div (Real.sqrt_nonneg 3),hroot,
    Real.rpow_neg hx.le]
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hs
    (inv_nonneg.mpr (Real.rpow_nonneg hx.le _))

theorem squared_error_to_quarter_bound (r ε K x : ℝ) (_hr : 0≤r) (hε : 0≤ε)
    (hK : 0≤K) (hx : 0<x) (h : r^2≤K*(ε^2+Real.sqrt (3/x))) :
    r≤(2*Real.sqrt K)*(ε+x^(-(1/4:ℝ))) := by
  have ht : 0≤ε^2+Real.sqrt (3/x) := by positivity
  have hrbound : r≤Real.sqrt K*Real.sqrt (ε^2+Real.sqrt (3/x)) := by
    have hs := Real.sq_sqrt hK
    have hs2 := Real.sq_sqrt ht
    have hmul : 0≤Real.sqrt K*Real.sqrt (ε^2+Real.sqrt (3/x)) := by positivity
    have he : (Real.sqrt K*Real.sqrt (ε^2+Real.sqrt (3/x)))^2 = K*(ε^2+Real.sqrt (3/x)) := by
      rw [mul_pow,hs,hs2]
    nlinarith
  have hsplit : Real.sqrt (ε^2+Real.sqrt (3/x))≤ε+Real.sqrt (Real.sqrt (3/x)) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hs := Real.sq_sqrt (Real.sqrt_nonneg (3/x))
      nlinarith [mul_nonneg hε (Real.sqrt_nonneg (Real.sqrt (3/x)))]
  have hq := nested_sqrt_prime_bound x hx
  calc
    r ≤ Real.sqrt K*(ε+Real.sqrt (Real.sqrt (3/x))) :=
      hrbound.trans (mul_le_mul_of_nonneg_left hsplit (Real.sqrt_nonneg K))
    _ ≤ Real.sqrt K*(ε+2*x^(-(1/4:ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hq) (Real.sqrt_nonneg K)
    _ ≤ (2*Real.sqrt K)*(ε+x^(-(1/4:ℝ))) := by
      nlinarith [mul_nonneg hε (Real.sqrt_nonneg K)]

end Ostmann.FiniteField

end OAI
