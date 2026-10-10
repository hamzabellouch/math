import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothMellinDerivatives

namespace OAI

/-! # Uniform Mellin decay of the fixed test in the required strip -/

namespace Ostmann

open MeasureTheory Finset
open scoped BigOperators Interval

theorem shiftedPrimeMeanMellin_product (n : ℕ) (s : ℂ) :
    shiftedPrimeMeanMellin n s =
      (-1 : ℂ) ^ n * (∏ j ∈ range n, (s + j)) * primeMeanMellin s := by
  induction n with
  | zero => simp [shiftedPrimeMeanMellin_zero]
  | succ n ih =>
    rw [shiftedPrimeMeanMellin_succ, ih, pow_succ, prod_range_succ]
    ring

/-- All shifted integrals needed below have a uniform bound on the fixed
half-unit interval. The power of t is bounded using only Re(s) >= -1/2. -/
theorem shiftedPrimeMeanMellin_norm_bound (n : ℕ) (s : ℂ) (D : ℝ)
    (hD : 0 ≤ D) (hd : ∀ t : ℝ, |iteratedDeriv n primeMeanTest t| ≤ D)
    (hs : -(1 / 2 : ℝ) ≤ s.re) :
    ‖shiftedPrimeMeanMellin n s‖ ≤ 4 * D := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := 1) (C := 4 * D)
    (f := fun t : ℝ => ((iteratedDeriv n primeMeanTest t : ℝ) : ℂ) *
      Complex.exp ((s + n - 1) * (Real.log t : ℂ))) (fun t ht => ?_)
  · change ‖shiftedPrimeMeanMellin n s‖ ≤ _ at hi
    norm_num at hi
    nlinarith
  rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hloglo : -Real.log 2 ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) ht.1.le
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one, zero_sub] at h
    exact h
  have hloghi : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
  have hcoef : -2 ≤ s.re + (n : ℝ) - 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcost : (s.re + (n : ℝ) - 1) * Real.log t ≤ 2 * Real.log 2 := by
    have h := mul_le_mul_of_nonpos_right hcoef hloghi
    linarith
  have he : ‖Complex.exp ((s + n - 1) * (Real.log t : ℂ))‖ ≤ 4 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.natCast_re,
      Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ Real.exp (2 * Real.log 2) := Real.exp_le_exp.mpr hcost
      _ = 4 := by rw [show (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ D * 4 := mul_le_mul (hd t) he (norm_nonneg _) hD
    _ = _ := by ring

/-- The product introduced by eight integrations by parts controls the
imaginary height without excluding real s. -/
theorem primeMeanMellin_height_bound (s : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ t : ℝ, |iteratedDeriv 8 primeMeanTest t| ≤ D)
    (hs : -(1 / 2 : ℝ) ≤ s.re) :
    |s.im| ^ 8 * ‖primeMeanMellin s‖ ≤ 4 * D := by
  have hp : |s.im| ^ 8 ≤ ∏ j ∈ range 8, ‖s + (j : ℕ)‖ := by
    have h := prod_le_prod₀ (f := fun _ : ℕ => |s.im|)
      (g := fun j : ℕ => ‖s + (j : ℂ)‖) (s := range 8)
      (fun j _ => abs_nonneg s.im) (fun j _ => ?_)
    · simpa using h
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
      Complex.abs_im_le_norm (s + (j : ℂ))
  calc
    _ ≤ (∏ j ∈ range 8, ‖s + (j : ℕ)‖) * ‖primeMeanMellin s‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = ‖shiftedPrimeMeanMellin 8 s‖ := by
      rw [shiftedPrimeMeanMellin_product, norm_mul, norm_mul, norm_pow, norm_neg, norm_one]
      simp only [one_pow, one_mul, norm_prod]
    _ ≤ _ := shiftedPrimeMeanMellin_norm_bound 8 s D hD hd hs

/-- The precise eighth-order decay field needed in the published explicit
formula structure is unconditional for the actual fixed test. -/
theorem primeMeanMellin_decay : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖primeMeanMellin s‖ ≤ C * Real.exp (-8 * Real.log (1 + |s.im|)) := by
  obtain ⟨D, hD, hd⟩ := primeMeanTest_iteratedDeriv_bound 8
  refine ⟨1024 * (D + 1), by positivity, ?_⟩
  intro s hs hs2
  have hb : ‖primeMeanMellin s‖ ≤ 4 := by
    have h := shiftedPrimeMeanMellin_norm_bound 0 s 1 (by norm_num) (fun t => ?_) hs
    · simpa only [shiftedPrimeMeanMellin_zero, mul_one] using h
    simp only [iteratedDeriv_zero]
    rw [abs_of_nonneg (primeMeanTest_nonneg t)]
    exact primeMeanTest_le_one t
  have hh := primeMeanMellin_height_bound s D hD.le hd hs
  have hm : ‖primeMeanMellin s‖ * (1 + |s.im|) ^ 8 ≤ 1024 * (D + 1) := by
    by_cases hsmall : |s.im| ≤ 1
    · have hpow : (1 + |s.im|) ^ 8 ≤ 256 := by
        calc
          _ ≤ (2 : ℝ) ^ 8 := pow_le_pow_left₀ (by positivity) (by linarith) 8
          _ = _ := by norm_num
      have h := mul_le_mul hb hpow (by positivity) (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith
    · have hlarge : 1 ≤ |s.im| := le_of_lt (lt_of_not_ge hsmall)
      have hpow : (1 + |s.im|) ^ 8 ≤ 256 * |s.im| ^ 8 := by
        calc
          _ ≤ (2 * |s.im|) ^ 8 := pow_le_pow_left₀ (by positivity) (by linarith) 8
          _ = _ := by ring
      have h := mul_le_mul_of_nonneg_left hpow (norm_nonneg (primeMeanMellin s))
      nlinarith
  have hx : 0 < 1 + |s.im| := by positivity
  have he : Real.exp (-8 * Real.log (1 + |s.im|)) = ((1 + |s.im|) ^ 8)⁻¹ := by
    rw [show -(8 : ℝ) * Real.log (1 + |s.im|) =
      -((8 : ℕ) * Real.log (1 + |s.im|)) by norm_num, Real.exp_neg,
      Real.exp_nat_mul, Real.exp_log hx]
  rw [he, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hx 8)).mpr hm

end Ostmann

end OAI
