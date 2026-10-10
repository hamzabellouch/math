import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterContinuation

namespace OAI

/-! The Mobius inverse bounds the reciprocal L-function on Re(s)=2
uniformly in the modulus. Combining this with the q-dependent Abel bound
gives growth of the normalized nonprincipal character L-function on a
fixed disk. No zero-free region is asserted here. -/

namespace TwoPointCorrelations

open Complex ArithmeticFunction
open scoped BigOperators Classical LSeries.notation ArithmeticFunction.Moebius

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterInverseConstant : ℝ :=
  1 + ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖

lemma mrtCharacterInverseConstant_pos : 0 < mrtCharacterInverseConstant := by
  unfold mrtCharacterInverseConstant
  have : 0 ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  linarith

omit [NeZero q] in
lemma mrtCharacter_twisted_moebius_norm (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ (n : ZMod q) * ((μ n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (show |μ n| ≤ 1 from abs_moebius_le_one)
  exact (mul_le_mul (χ.norm_le_one _) hμ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

omit [NeZero q] in
lemma mrtCharacter_inverse_series_norm_le (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.re = 2) :
    ‖LSeries (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s‖ ≤
      mrtCharacterInverseConstant := by
  have hσ : 1 < s.re := by rw [hs]; norm_num
  have hm := χ.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hσ)
  have hbase : Summable (fun n : ℕ => ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖) :=
    (LSeriesSummable_one_iff.mpr (by norm_num : 1 < (2 : ℂ).re)).norm
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hm.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ := by
      apply Summable.tsum_le_tsum (fun n => ?_) hm.norm hbase
      simp only [LSeries.norm_term_eq, hs, Complex.re_ofNat, Pi.one_apply, norm_one]
      split_ifs with hn
      · rfl
      · exact div_le_div_of_nonneg_right (mrtCharacter_twisted_moebius_norm χ n)
          (Real.rpow_nonneg n.cast_nonneg _)
    _ ≤ mrtCharacterInverseConstant := by unfold mrtCharacterInverseConstant; linarith

/-- Uniform reciprocal bound, independent of the imaginary part and character. -/
theorem mrtCharacter_LFunction_inv_norm (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.re = 2) :
    ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ mrtCharacterInverseConstant := by
  have hσ : 1 < s.re := by rw [hs]; norm_num
  have heq := DirichletCharacter.LSeries.mul_mu_eq_one χ hσ
  have hn := χ.LSeries_ne_zero_of_one_lt_re hσ
  have hi : (LSeries (fun n => χ (n : ZMod q)) s)⁻¹ =
      LSeries (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s := by
    apply (mul_left_cancel₀ hn)
    simpa only [mul_inv_cancel₀ hn, Pi.mul_def] using heq.symm
  rw [DirichletCharacter.LFunction_eq_LSeries χ hσ, hi]
  exact mrtCharacter_inverse_series_norm_le χ hs

noncomputable def mrtCharacterNormalizedLFunction (χ : DirichletCharacter ℂ q) (t : ℝ)
    (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z) /
    DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ))

lemma mrtCharacterNormalizedLFunction_zero (χ : DirichletCharacter ℂ q) (t : ℝ) :
    mrtCharacterNormalizedLFunction χ t 0 = 1 := by
  simp only [mrtCharacterNormalizedLFunction, mul_zero, add_zero]
  exact div_self (χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
    intro h; have := congrArg Complex.re h; norm_num at this)) (by norm_num))

lemma mrtCharacterNormalizedLFunction_differentiable (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) :
    Differentiable ℂ (mrtCharacterNormalizedLFunction χ t) := by
  unfold mrtCharacterNormalizedLFunction
  have ha : Differentiable ℂ (fun z : ℂ => (2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z) := by
    fun_prop
  exact ((DirichletCharacter.differentiable_LFunction hχ).comp ha).div_const _

lemma mrtCharacterNormalizedLFunction_norm (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖mrtCharacterNormalizedLFunction χ t z‖ ≤
      (2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4) := by
  have hC : 0 ≤ mrtCharacterInverseConstant := mrtCharacterInverseConstant_pos.le
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
  have hn := mrt_character_LFunction_norm_halfPlane χ hχ hs
  have hi := mrtCharacter_LFunction_inv_norm χ (s := (2 : ℂ) + Complex.I * (t : ℂ))
    (by simp)
  unfold mrtCharacterNormalizedLFunction
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ ((2 * q : ℝ) * ‖s‖) * mrtCharacterInverseConstant :=
      mul_le_mul hn hi (norm_nonneg _) (by positivity)
    _ = ((2 * q : ℝ) * mrtCharacterInverseConstant) * ‖s‖ := by ring
    _ ≤ ((2 * q : ℝ) * mrtCharacterInverseConstant) * (|t| + 4) :=
      mul_le_mul_of_nonneg_left hsbound (by positivity)

end TwoPointCorrelations

end OAI
