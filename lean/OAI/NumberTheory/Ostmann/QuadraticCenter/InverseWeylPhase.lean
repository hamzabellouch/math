import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open Finset

noncomputable def weylPhase (x : ℝ) : ℂ := Real.fourierChar x

@[simp] theorem weylPhase_norm (x : ℝ) : ‖weylPhase x‖ = 1 := Circle.norm_coe _
@[simp] theorem weylPhase_zero : weylPhase 0 = 1 := by simp [weylPhase]
theorem weylPhase_add (x y : ℝ) : weylPhase (x+y) = weylPhase x*weylPhase y := by
  simp [weylPhase, AddChar.map_add_eq_mul]
theorem weylPhase_sub (x y : ℝ) : weylPhase (x-y) = weylPhase x/weylPhase y := by
  simp [weylPhase, AddChar.map_sub_eq_div]
@[simp] theorem weylPhase_int (n : ℤ) : weylPhase n = 1 := by
  change ((Circle.exp (2*Real.pi*n) : Circle) : ℂ) = 1
  rw [mul_comm, Circle.exp_int_mul_two_pi, Circle.coe_one]
theorem weylPhase_sub_int (x : ℝ) (n : ℤ) : weylPhase (x-n) = weylPhase x := by
  rw [weylPhase_sub, weylPhase_int, div_one]
theorem weylPhase_nat_mul (x : ℝ) (n : ℕ) : weylPhase (n*x) = weylPhase x^n := by
  simp only [weylPhase, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

noncomputable def integerDistance (x : ℝ) : ℝ := |x-(round x : ℤ)|
theorem integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := abs_nonneg _
theorem integerDistance_le_half (x : ℝ) : integerDistance x ≤ 1/2 := abs_sub_round x
theorem integerDistance_le (x : ℝ) (n : ℤ) : integerDistance x ≤ |x-n| := round_le x n

theorem phase_sub_one_lower (x : ℝ) : 4*integerDistance x ≤ ‖weylPhase x-1‖ := by
  let y : ℝ := x-(round x : ℤ)
  have hy : |y| ≤ 1/2 := abs_sub_round x
  have he : weylPhase y = weylPhase x := weylPhase_sub_int x (round x)
  rw [← he]
  have heq : weylPhase y = Complex.exp (Complex.I*(2*Real.pi*y : ℝ)) := by
    rw [weylPhase, Real.fourierChar_apply, mul_comm]
  rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [show 2*Real.pi*y/2 = Real.pi*y by ring]
  have harg : |Real.pi*y| ≤ Real.pi/2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hm : 2/Real.pi*(Real.pi*|y|) = 2*|y| := by field_simp
  rw [hm] at hsin
  have hd : integerDistance x = |y| := rfl
  rw [hd]
  nlinarith only [hsin]

theorem linear_weyl_bound (x : ℝ) (N : ℕ) :
    ‖∑ n ∈ range N, weylPhase ((n:ℝ)*x)‖ ≤ N ∧
    ‖∑ n ∈ range N, weylPhase ((n:ℝ)*x)‖*integerDistance x ≤ 1/2 := by
  have htriv : ‖∑ n ∈ range N, weylPhase ((n:ℝ)*x)‖ ≤ N := by
    calc
      _ ≤ ∑ n ∈ range N, ‖weylPhase ((n:ℝ)*x)‖ := norm_sum_le _ _
      _ = _ := by simp
  refine ⟨htriv, ?_⟩
  have hgeom := congrArg norm (geom_sum_mul (weylPhase x) N)
  rw [norm_mul] at hgeom
  have hnum : ‖weylPhase x^N-1‖ ≤ 2 := by
    calc
      _ ≤ ‖weylPhase x^N‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _ = _ := by norm_num [norm_pow]
  have hl := phase_sub_one_lower x
  have hmul := mul_le_mul_of_nonneg_left hl
    (norm_nonneg (∑ n ∈ range N, weylPhase x^n))
  rw [hgeom] at hmul
  simp only [weylPhase_nat_mul]
  nlinarith

end Ostmann.QuadraticCenter

end OAI
