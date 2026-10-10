import OAI.NumberTheory.TwoPoint.Fourier.ModFiveAbelContinuation

namespace OAI

/-! Uniform lower bounds on `Re s = 2`, from the exact Möbius inverse.
Together with the Abel upper bound these give the polynomial bound for a
normalized analytic disk used in the fixed-modulus zero-free argument.
-/

namespace TwoPointCorrelations

open Complex ArithmeticFunction
open scoped BigOperators Classical LSeries.notation ArithmeticFunction.Moebius

noncomputable def modFiveInverseConstant : ℝ :=
  1 + ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖

lemma modFiveInverseConstant_pos : 0 < modFiveInverseConstant := by
  unfold modFiveInverseConstant
  have : 0 ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  linarith

lemma modFive_twisted_moebius_norm (χ : DirichletCharacter ℂ 5) (n : ℕ) :
    ‖χ (n : ZMod 5) * ((μ n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (show |μ n| ≤ 1 from abs_moebius_le_one)
  exact (mul_le_mul (χ.norm_le_one _) hμ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

lemma modFive_inverse_series_norm_le (χ : DirichletCharacter ℂ 5)
    {s : ℂ} (hs : s.re = 2) :
    ‖LSeries (fun n => χ (n : ZMod 5) * ((μ n : ℤ) : ℂ)) s‖ ≤
      modFiveInverseConstant := by
  have hσ : 1 < s.re := by rw [hs]; norm_num
  have hm := χ.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hσ)
  have hbase : Summable (fun n : ℕ => ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖) :=
    (LSeriesSummable_one_iff.mpr (by norm_num : 1 < (2 : ℂ).re)).norm
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n => χ (n : ZMod 5) * ((μ n : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hm.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ := by
      apply Summable.tsum_le_tsum (fun n => ?_) hm.norm hbase
      simp only [LSeries.norm_term_eq, hs, Complex.re_ofNat, Pi.one_apply, norm_one]
      split_ifs with hn
      · rfl
      · exact div_le_div_of_nonneg_right (modFive_twisted_moebius_norm χ n)
          (Real.rpow_nonneg n.cast_nonneg _)
    _ ≤ modFiveInverseConstant := by unfold modFiveInverseConstant; linarith

/-- Uniform reciprocal bound, independent of the imaginary part and character. -/
theorem modFive_LFunction_inv_norm (χ : DirichletCharacter ℂ 5)
    {s : ℂ} (hs : s.re = 2) :
    ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ modFiveInverseConstant := by
  have hσ : 1 < s.re := by rw [hs]; norm_num
  have heq := DirichletCharacter.LSeries.mul_mu_eq_one χ hσ
  have hn := χ.LSeries_ne_zero_of_one_lt_re hσ
  have hi : (LSeries (fun n => χ (n : ZMod 5)) s)⁻¹ =
      LSeries (fun n => χ (n : ZMod 5) * ((μ n : ℤ) : ℂ)) s := by
    apply (mul_left_cancel₀ hn)
    simpa only [mul_inv_cancel₀ hn, Pi.mul_def] using heq.symm
  rw [DirichletCharacter.LFunction_eq_LSeries χ hσ, hi]
  exact modFive_inverse_series_norm_le χ hs

noncomputable def modFiveNormalizedLFunction (χ : DirichletCharacter ℂ 5) (t : ℝ)
    (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z) /
    DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ))

lemma modFiveNormalizedLFunction_zero (χ : DirichletCharacter ℂ 5) (t : ℝ) :
    modFiveNormalizedLFunction χ t 0 = 1 := by
  simp only [modFiveNormalizedLFunction, mul_zero, add_zero]
  exact div_self (χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
    intro h; have := congrArg Complex.re h; norm_num at this)) (by norm_num))

lemma modFiveNormalizedLFunction_differentiable (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (t : ℝ) :
    Differentiable ℂ (modFiveNormalizedLFunction χ t) := by
  unfold modFiveNormalizedLFunction
  have ha : Differentiable ℂ (fun z : ℂ => (2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z) := by
    fun_prop
  exact ((DirichletCharacter.differentiable_LFunction hχ).comp ha).div_const _

lemma modFiveNormalizedLFunction_norm (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖modFiveNormalizedLFunction χ t z‖ ≤
      8 * modFiveInverseConstant * (|t| + 4) := by
  let s : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z
  have hr : -(1 : ℝ) ≤ z.re := by
    have h := (abs_re_le_norm z).trans hz
    exact (abs_le.mp h).1
  have hs : (1 / 2 : ℝ) ≤ s.re := by
    norm_num [s, Complex.mul_re]
    linarith
  have hsbound : ‖s‖ ≤ |t| + 4 := by
    calc
      ‖s‖ ≤ ‖(2 : ℂ) + Complex.I * (t : ℂ)‖ + ‖(3 / 2 : ℂ) * z‖ := norm_add_le _ _
      _ ≤ (‖(2 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖) + ‖(3 / 2 : ℂ) * z‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = 2 + |t| + (3 / 2 : ℝ) * ‖z‖ := by
        norm_num [norm_mul]
      _ ≤ |t| + 4 := by linarith
  have hn := modFive_LFunction_norm_halfPlane χ hχ hs
  have hi := modFive_LFunction_inv_norm χ (s := (2 : ℂ) + Complex.I * (t : ℂ))
    (by simp)
  unfold modFiveNormalizedLFunction
  rw [div_eq_mul_inv, norm_mul]
  exact (mul_le_mul hn hi (norm_nonneg _) (by positivity)).trans (by
    nlinarith [modFiveInverseConstant_pos])

end TwoPointCorrelations

end OAI
