import Mathlib

namespace OAI

/-! Poisson summation for shifted Gaussian functions on the hexagonal lattice. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment.HeckeTheta

def hexQ (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2

lemma hexQ_lower (x y : ℝ) : (x ^ 2 + y ^ 2) / 2 ≤ hexQ x y := by
  unfold hexQ
  nlinarith [sq_nonneg (x - y)]

lemma completed_square (x y : ℝ) : hexQ x y = (x - y / 2) ^ 2 + 3 * y ^ 2 / 4 := by
  unfold hexQ
  ring

 

def EisensteinGaussianPoissonStatement : Prop :=
  ∀ (t x y : ℝ), 0 < t →
    (∑' n : ℤ, ∑' m : ℤ,
      Complex.exp (-(Real.pi : ℂ) * t * (hexQ (m + x) (n + y) : ℂ))) =
    (2 / ((Real.sqrt 3 : ℂ) * t)) *
      ∑' h : ℤ, ∑' k : ℤ,
        Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t) *
          (((h : ℂ) ^ 2 + h * k + (k : ℂ) ^ 2))) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((h : ℂ) * x + (k : ℂ) * y))

lemma summable_cexp_quadratic {a : ℂ} (ha : a.re < 0) (b c : ℂ) :
    Summable (fun n : ℤ => Complex.exp (a * (n : ℂ) ^ 2 + b * n + c)) := by
  have h := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact ha b (-2)).isBigO
  have hs : Summable (fun n : ℤ => Complex.exp (a * (n : ℂ) ^ 2 + b * n)) := by
    exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (h.comp_tendsto Int.tendsto_coe_cofinite)
  simpa only [Complex.exp_add] using hs.mul_right (Complex.exp c)

lemma first_poisson_exponent (a b c n h : ℂ) (ha : a ≠ 0) :
    (-(Real.pi : ℂ) * a * n ^ 2 + 2 * Real.pi * c * n) -
      (Real.pi : ℂ) / a * (h + Complex.I * (b + a * n / 2)) ^ 2 =
    -(Real.pi : ℂ) / a * (h + Complex.I * b) ^ 2 -
      3 * Real.pi * a / 4 * n ^ 2 +
      2 * Real.pi * (c + b / 2 - Complex.I * h / 2) * n := by
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma shifted_gaussian_exponent (a b x n : ℂ) :
    -(Real.pi : ℂ) * a * (n + x) ^ 2 + 2 * Real.pi * I * b * (n + x) =
    (-(Real.pi : ℂ) * a * n ^ 2 + 2 * Real.pi * (-a * x + I * b) * n) +
      (-(Real.pi : ℂ) * a * x ^ 2 + 2 * Real.pi * I * b * x) := by ring

lemma shifted_gaussian_dual_exponent (a b x k : ℂ) (ha : a ≠ 0) :
    (-(Real.pi : ℂ) * a * x ^ 2 + 2 * Real.pi * I * b * x) -
      Real.pi / a * (k + I * (-a * x + I * b)) ^ 2 =
    -(Real.pi : ℂ) / a * (k - b) ^ 2 + 2 * Real.pi * I * k * x := by
  field_simp
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

 
lemma shifted_gaussian_poisson (a x b : ℝ) (ha : 0 < a) :
    (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * a * ((n : ℂ) + x) ^ 2 +
        2 * Real.pi * I * b * ((n : ℂ) + x))) =
      (1 / (Real.sqrt a : ℂ)) * ∑' k : ℤ,
        Complex.exp (-(Real.pi : ℂ) / a * ((k : ℂ) - b) ^ 2 +
          2 * Real.pi * I * k * x) := by
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hsqrt : (a : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
    norm_num
  conv_lhs =>
    arg 1
    ext n
    rw [shifted_gaussian_exponent, Complex.exp_add]
  rw [tsum_mul_right,
    Complex.tsum_exp_neg_quadratic (by simpa using ha : 0 < (a : ℂ).re), hsqrt]
  rw [mul_assoc, ← tsum_mul_right]
  congr 1
  apply tsum_congr
  intro k
  rw [← Complex.exp_add]
  congr 1
  have h := shifted_gaussian_dual_exponent (a : ℂ) b x k hac
  linear_combination h

lemma shifted_gaussian_summable (a x : ℝ) (ha : 0 < a) :
    Summable (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) * a * ((n : ℂ) + x) ^ 2)) := by
  have hneg : (-(Real.pi : ℂ) * a).re < 0 := by
    simpa using neg_neg_of_pos (mul_pos Real.pi_pos ha)
  convert summable_cexp_quadratic hneg (-2 * Real.pi * a * x)
    (-Real.pi * a * (x : ℂ) ^ 2) using 1
  ext n
  congr 1
  ring

lemma norm_real_phase (r : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * I * r)‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re]

def middle (t x y : ℝ) (n h : ℤ) : ℂ :=
  Complex.exp (-(3 * (Real.pi : ℂ)) * t / 4 * ((n : ℂ) + y) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / t * (h : ℂ) ^ 2) *
    Complex.exp (2 * (Real.pi : ℂ) * I * h * (x - ((n : ℂ) + y) / 2))

lemma middle_phase_norm (x y : ℝ) (n h : ℤ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * I * h * (x - ((n : ℂ) + y) / 2))‖ = 1 := by
  convert norm_real_phase ((h : ℝ) * (x - ((n : ℝ) + y) / 2)) using 2
  push_cast
  ring_nf

lemma middle_summable (t x y : ℝ) (ht : 0 < t) :
    Summable (Function.uncurry (middle t x y)) := by
  have hf := shifted_gaussian_summable (3 * t / 4) y (by positivity)
  have hg := shifted_gaussian_summable (1 / t) 0 (by positivity)
  have hp := hf.norm.mul_norm hg.norm
  refine hp.of_norm_bounded fun nh => le_of_eq ?_
  rcases nh with ⟨n, h⟩
  dsimp [Function.uncurry, middle]
  rw [norm_mul, middle_phase_norm, mul_one]
  congr 2 <;> congr 1 <;> push_cast <;> ring

lemma eisenstein_first_exponent (t x y : ℝ) (n m : ℤ) :
    -(Real.pi : ℂ) * t * (hexQ ((m : ℝ) + x) ((n : ℝ) + y) : ℂ) =
      -(3 * (Real.pi : ℂ)) * t / 4 * ((n : ℂ) + y) ^ 2 +
      (-(Real.pi : ℂ) * t * ((m : ℂ) + (x - ((n : ℂ) + y) / 2)) ^ 2) := by
  unfold hexQ
  push_cast
  ring

lemma first_poisson_step (t x y : ℝ) (ht : 0 < t) (n : ℤ) :
    (∑' m : ℤ,
      Complex.exp (-(Real.pi : ℂ) * t * (hexQ (m + x) (n + y) : ℂ))) =
      (1 / (Real.sqrt t : ℂ)) * ∑' h : ℤ, middle t x y n h := by
  let r : ℝ := x - ((n : ℝ) + y) / 2
  let C : ℂ := Complex.exp (-(3 * (Real.pi : ℂ)) * t / 4 * ((n : ℂ) + y) ^ 2)
  have hfirst := shifted_gaussian_poisson t r 0 ht
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, add_zero, sub_zero] at hfirst
  calc
    _ = C * ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * t * ((m : ℂ) + r) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      dsimp [C, r]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      exact eisenstein_first_exponent t x y n m
    _ = C * ((1 / (Real.sqrt t : ℂ)) * ∑' h : ℤ,
        Complex.exp (-(Real.pi : ℂ) / t * (h : ℂ) ^ 2 + 2 * Real.pi * I * h * r)) := by
      rw [hfirst]
    _ = _ := by
      rw [mul_left_comm, ← tsum_mul_left]
      congr 1
      apply tsum_congr
      intro h
      dsimp [C, middle, r]
      push_cast
      rw [Complex.exp_add]
      ring

lemma second_poisson_exponent (t : ℂ) (ht : t ≠ 0) (h k : ℂ) :
    -(Real.pi : ℂ) / t * h ^ 2 - Real.pi / (3 * t / 4) * (k + h / 2) ^ 2 =
      -(4 * (Real.pi : ℂ)) / (3 * t) * (h ^ 2 + h * k + k ^ 2) := by
  field_simp
  ring

lemma second_poisson_step (t x y : ℝ) (ht : 0 < t) (h : ℤ) :
    (∑' n : ℤ, middle t x y n h) =
      (1 / (Real.sqrt (3 * t / 4) : ℂ)) * ∑' k : ℤ,
        Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t) *
          ((h : ℂ) ^ 2 + h * k + (k : ℂ) ^ 2)) *
        Complex.exp (2 * (Real.pi : ℂ) * I * ((h : ℂ) * x + (k : ℂ) * y)) := by
  let a : ℝ := 3 * t / 4
  let b : ℝ := -(h : ℝ) / 2
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / t * (h : ℂ) ^ 2 +
    2 * Real.pi * I * h * x)
  have hsecond := shifted_gaussian_poisson a y b (by dsimp [a]; positivity)
  calc
    _ = C * ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * a * ((n : ℂ) + y) ^ 2 +
          2 * Real.pi * I * b * ((n : ℂ) + y)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      dsimp [middle, C, a, b]
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = C * ((1 / (Real.sqrt a : ℂ)) * ∑' k : ℤ,
        Complex.exp (-(Real.pi : ℂ) / a * ((k : ℂ) - b) ^ 2 +
          2 * Real.pi * I * k * y)) := by rw [hsecond]
    _ = _ := by
      rw [mul_left_comm, ← tsum_mul_left]
      congr 1
      apply tsum_congr
      intro k
      dsimp [C, a, b]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      have hk := second_poisson_exponent (t : ℂ) (by exact_mod_cast ht.ne') h k
      linear_combination hk

lemma poisson_normalization (t : ℝ) (ht : 0 < t) :
    (1 / (Real.sqrt t : ℂ)) * (1 / (Real.sqrt (3 * t / 4) : ℂ)) =
      2 / ((Real.sqrt 3 : ℂ) * t) := by
  have hs : Real.sqrt (3 * t / 4) = Real.sqrt 3 * Real.sqrt t / 2 := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs]
  push_cast
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hst0 : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hs30 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hst : (Real.sqrt t : ℂ) ^ 2 = t := by
    exact_mod_cast Real.sq_sqrt ht.le
  field_simp
  linear_combination -hst

 

theorem eisenstein_gaussian_poisson : EisensteinGaussianPoissonStatement := by
  intro t x y ht
  simp_rw [first_poisson_step t x y ht]
  rw [tsum_mul_left, ← (middle_summable t x y ht).tsum_comm]
  simp_rw [second_poisson_step t x y ht]
  rw [tsum_mul_left, ← mul_assoc, poisson_normalization t ht]

lemma hex_gaussian_summable (t x y : ℝ) (ht : 0 < t) :
    Summable (fun nm : ℤ × ℤ => Complex.exp (-(Real.pi : ℂ) * t *
      (hexQ ((nm.2 : ℝ) + x) ((nm.1 : ℝ) + y) : ℂ))) := by
  have h1 := shifted_gaussian_summable (t / 2) y (by positivity)
  have h2 := shifted_gaussian_summable (t / 2) x (by positivity)
  refine (h1.norm.mul_norm h2.norm).of_norm_bounded fun nm => ?_
  rcases nm with ⟨n, m⟩
  simp only [norm_mul, ← Complex.ofReal_intCast, ← Complex.ofReal_add,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_pow,
    Complex.norm_exp_ofReal]
  rw [← Real.exp_add, Real.exp_le_exp]
  have hb := mul_le_mul_of_nonneg_left (hexQ_lower ((m : ℝ) + x) ((n : ℝ) + y))
    (mul_pos Real.pi_pos ht).le
  nlinarith
end CubicFirstMoment.HeckeTheta
end

end OAI
