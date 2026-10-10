import Mathlib.Tactic.FieldSimp
import OAI.NumberTheory.Ostmann.ZeroDensity.RemainderDecay

namespace OAI

noncomputable section
namespace Ostmann.ZeroDensity

theorem contour_polynomial_ratio_le (B : ℕ) {Q H : ℝ} (hQ : 0 < Q) (hH : 2 ≤ H) :
    (Q*(H+2))^B/H^(B+1) ≤ (2 : ℝ)^B*Q^B/H := by
  have hHp : 0 < H := by linarith
  calc
    _ ≤ (Q*(2*H))^B/H^(B+1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    _ = _ := by
      rw [mul_pow,mul_pow,pow_succ]
      field_simp

theorem contour_tail_power_bound (B : ℕ) {Q H X E L : ℝ}
    (hQ : 0 < Q) (hH : 2 ≤ H) (hL : 0 ≤ L)
    (hXlog : 0 ≤ Real.log X) (hXupper : Real.log X ≤ 2*Real.exp L)
    (hheight : Q^(B+2)*Real.exp (E*L) ≤ H) :
    Q^2*(Q*(H+2))^B/H^(B+1)*(1+Real.log X)^B ≤
      (6 : ℝ)^B*Real.exp (((B : ℝ)-E)*L) := by
  have hHp : 0 < H := by linarith
  have hE : 0 < Real.exp (E*L) := Real.exp_pos _
  have hratio : Q^(B+2)/H ≤ Real.exp (-E*L) := by
    calc
      _ ≤ Q^(B+2)/(Q^(B+2)*Real.exp (E*L)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hheight
      _ = _ := by
        rw [show -E*L = -(E*L) by ring, Real.exp_neg]
        field_simp
  have hlogbound : 1+Real.log X ≤ 3*Real.exp L := by
    have he := Real.one_le_exp hL
    linarith
  have hpoly := contour_polynomial_ratio_le B hQ hH
  calc
    _ = Q^2*((Q*(H+2))^B/H^(B+1))*(1+Real.log X)^B := by ring
    _ ≤ Q^2*((2 : ℝ)^B*Q^B/H)*(3*Real.exp L)^B := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpoly (sq_nonneg _)
      · exact pow_le_pow_left₀ (by positivity) hlogbound B
      · positivity
      · positivity
    _ = (6 : ℝ)^B*(Q^(B+2)/H)*(Real.exp L)^B := by
      rw [show (6 : ℝ)=2*3 by norm_num,mul_pow,mul_pow,pow_add]
      ring
    _ ≤ (6 : ℝ)^B*Real.exp (-E*L)*(Real.exp L)^B := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      ring

end Ostmann.ZeroDensity

end

end OAI
