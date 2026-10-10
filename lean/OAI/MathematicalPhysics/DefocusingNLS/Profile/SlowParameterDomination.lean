import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowAsymptoticBound
import Mathlib.Analysis.Complex.Liouville

namespace OAI

/-! # Uniform parameter bounds for the regularized kernel

The cancellation bound is uniform for bounded exponents. Cauchy's estimate
will then control parameter derivatives without a separate logarithmic
endpoint estimate.
-/

open MeasureTheory

namespace DefocusingNLS

theorem one_le_norm_one_add_real_div (x : ℂ) (hx : 0 ≤ x.re)
    {u : ℝ} (hu : 0 ≤ u) : 1 ≤ ‖1 + (u : ℂ) / x‖ := by
  apply le_trans (b := (1 + (u : ℂ) / x).re) _ (Complex.re_le_norm _)
  simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, zero_div, add_zero]
  have : 0 ≤ u * x.re / Complex.normSq x :=
    div_nonneg (mul_nonneg hu hx) (Complex.normSq_nonneg x)
  linarith

theorem regularizingBracket_bounded_exponents (r x : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ‖r‖ ≤ M) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    ‖regularizingBracket r x u‖ ≤
      (M * Real.exp (Real.pi * M) / ‖x‖) * u * (1 + u / ‖x‖) ^ (M + 1) := by
  let C : ℝ := M * Real.exp (Real.pi * M) / ‖x‖ * (1 + u / ‖x‖) ^ (M + 1)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hd (v : ℝ) (hv : v ∈ Set.Icc 0 u) :=
    hasDerivAt_regularizingBracket_real r x hx hv.1
  have hb (v : ℝ) (hv : v ∈ Set.Ico 0 u) :
      ‖r * (1 + (v : ℂ) / x) ^ (r - 1) / x‖ ≤ C := by
    have hn := one_le_norm_one_add_real_div x hx hv.1
    have hup : ‖1 + (v : ℂ) / x‖ ≤ 1 + u / ‖x‖ := by
      calc
        _ ≤ 1 + v / ‖x‖ := by
          simpa only [norm_one, norm_div, Complex.norm_of_nonneg hv.1] using
            norm_add_le (1 : ℂ) ((v : ℂ) / x)
        _ ≤ _ := by gcongr; exact hv.2.le
    have he : max (r - 1).re 0 ≤ M + 1 := by
      have hre : r.re ≤ M := (Complex.re_le_norm r).trans hr
      simp only [Complex.sub_re, Complex.one_re]
      exact max_le (by linarith) (by linarith)
    have him : |(r - 1).im| ≤ M := by
      simpa using (Complex.abs_im_le_norm r).trans hr
    have hp : ‖(1 + (v : ℂ) / x) ^ (r - 1)‖ ≤
        Real.exp (Real.pi * M) * (1 + u / ‖x‖) ^ (M + 1) := by
      apply (norm_cpow_le_rpow_max _ _ hn).trans
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left him Real.pi_pos.le
      · exact (Real.rpow_le_rpow_of_exponent_le hn he).trans
          (Real.rpow_le_rpow (norm_nonneg _) hup (by linarith))
      · positivity
      · positivity
    calc
      _ = ‖r‖ * ‖(1 + (v : ℂ) / x) ^ (r - 1)‖ / ‖x‖ := by rw [norm_div, norm_mul]
      _ ≤ M * (Real.exp (Real.pi * M) * (1 + u / ‖x‖) ^ (M + 1)) / ‖x‖ := by
        gcongr
      _ = C := by dsimp [C]; ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun v hv => (hd v hv).hasDerivWithinAt) hb u ⟨hu, le_rfl⟩
  simp only [regularizingBracket, Complex.ofReal_zero, zero_div, add_zero,
    Complex.one_cpow, sub_self, sub_zero] at h
  calc
    _ ≤ C * u := h
    _ = _ := by dsimp [C]; ring

theorem regularizedSlowKernel_bounded_parameters (q : ℂ) (m : ℕ) (x : ℂ)
    (a b M : ℝ) (hM : 0 ≤ M) (hqa : a ≤ q.re) (hqb : q.re ≤ b)
    (hqm : ‖(m : ℂ) - 1 - q‖ ≤ M) (hx : 0 ≤ x.re) (hx0 : x ≠ 0)
    {u : ℝ} (hu : 0 < u) :
    ‖regularizedSlowKernel q m x u‖ ≤
      (M * Real.exp (Real.pi * M) / ‖x‖ * (1 + ‖x‖⁻¹) ^ (M + 1)) *
        (Real.exp (-u) * u ^ a + Real.exp (-u) * u ^ b +
          Real.exp (-u) * u ^ (a + (M + 1)) + Real.exp (-u) * u ^ (b + (M + 1))) := by
  let A : ℝ := M + 1
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hb := regularizingBracket_bounded_exponents ((m : ℂ) - 1 - q) x M hM hqm hx hx0 hu.le
  have hp : u ^ q.re ≤ u ^ a + u ^ b := by
    rcases le_total u 1 with hu1 | hu1
    · exact (Real.rpow_le_rpow_of_exponent_ge hu hu1 hqa).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hu.le b))
    · exact (Real.rpow_le_rpow_of_exponent_le hu1 hqb).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hu.le a))
  have hpow : u ^ (q.re - 1) * u = u ^ q.re := by
    calc
      _ = u ^ (q.re - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ (q.re - 1 + 1) := (Real.rpow_add hu _ _).symm
      _ = _ := by congr 1; ring
  calc
    ‖regularizedSlowKernel q m x u‖ = Real.exp (-u) * u ^ (q.re - 1) *
        ‖regularizingBracket ((m : ℂ) - 1 - q) x u‖ := by
      simp only [regularizedSlowKernel, norm_mul, Complex.norm_exp, Complex.neg_re,
        Complex.ofReal_re, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re, Complex.one_re]
    _ ≤ Real.exp (-u) * u ^ (q.re - 1) *
        ((M * Real.exp (Real.pi * M) / ‖x‖) * u * (1 + u / ‖x‖) ^ A) := by gcongr
    _ = (M * Real.exp (Real.pi * M) / ‖x‖) * Real.exp (-u) * u ^ q.re *
        (1 + u / ‖x‖) ^ A := by rw [← hpow]; ring
    _ ≤ (M * Real.exp (Real.pi * M) / ‖x‖) * Real.exp (-u) * (u ^ a + u ^ b) *
        ((1 + ‖x‖⁻¹) ^ A * (1 + u ^ A)) := by
      gcongr
      exact one_add_div_rpow_le ‖x‖ A u hxpos (by dsimp [A]; linarith) hu.le
    _ = _ := by
      dsimp [A]
      rw [Real.rpow_add hu a (M + 1), Real.rpow_add hu b (M + 1)]
      ring

theorem exists_regularizedSlowKernel_majorant (m : ℕ) (x : ℂ) (a b M : ℝ)
    (ha : -1 < a) (hM : 0 ≤ M) (hab : a ≤ b) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    ∃ bound : ℝ → ℝ, IntegrableOn bound (Set.Ioi 0) ∧
      ∀ q : ℂ, a ≤ q.re → q.re ≤ b → ‖(m : ℂ) - 1 - q‖ ≤ M →
        ∀ u : ℝ, 0 < u → ‖regularizedSlowKernel q m x u‖ ≤ bound u := by
  let C : ℝ := M * Real.exp (Real.pi * M) / ‖x‖ * (1 + ‖x‖⁻¹) ^ (M + 1)
  refine ⟨fun u => C * (Real.exp (-u) * u ^ a + Real.exp (-u) * u ^ b +
      Real.exp (-u) * u ^ (a + (M + 1)) + Real.exp (-u) * u ^ (b + (M + 1))), ?_, ?_⟩
  · apply Integrable.const_mul
    exact (((integrable_exp_neg_mul_rpow a ha).add
      (integrable_exp_neg_mul_rpow b (ha.trans_le hab))).add
        (integrable_exp_neg_mul_rpow (a + (M + 1)) (by linarith))).add
          (integrable_exp_neg_mul_rpow (b + (M + 1)) (by linarith))
  · intro q hqa hqb hqm u hu
    exact regularizedSlowKernel_bounded_parameters q m x a b M hM hqa hqb hqm hx hx0 hu

end DefocusingNLS

end OAI
