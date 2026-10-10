import OAI.NumberTheory.TwoPointCorrelations.ModFiveAbelContinuation

namespace OAI

/-! The de la Vallée Poussin positivity inequality for modulus five.
The proof is termwise and uses the actual Mangoldt Dirichlet series.
It does not assume a zero-free region or a prime-number estimate.
-/

namespace TwoPointCorrelations

open Complex ArithmeticFunction
open scoped BigOperators Classical LSeries.notation

lemma modFive_three_four_one_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hn : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have := sq_le_sq₀ (norm_nonneg z) zero_le_one |>.mpr hz
    simpa only [Complex.sq_norm, Complex.normSq_apply, ← sq, one_pow] using this
  have hs := sq_nonneg (z.re + 1)
  simp only [pow_two, Complex.mul_re]
  nlinarith

lemma modFive_phase_norm (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ‖(n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

lemma modFive_twisted_phase_norm (χ : DirichletCharacter ℂ 5)
    (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ‖χ (n : ZMod 5) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1 := by
  rw [norm_mul, modFive_phase_norm n hn t, mul_one]
  exact χ.norm_le_one _

lemma modFive_real_mangoldt_term (σ : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n =
      ((vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_mul]

lemma modFive_twisted_mangoldt_term (χ : DirichletCharacter ℂ 5)
    (σ t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (modFiveMangoldtTwist χ) ((σ : ℂ) + Complex.I * (t : ℂ)) n =
      ((vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        (χ (n : ZMod 5) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
    Complex.cpow_add _ _ (by exact_mod_cast hn)]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow n.cast_nonneg]
  simp only [modFiveMangoldtTwist, Complex.ofReal_mul]
  ring

lemma modFive_double_phase (χ : DirichletCharacter ℂ 5) (n : ℕ) (t : ℝ) :
    (χ ^ 2) (n : ZMod 5) * (n : ℂ) ^ (-(Complex.I * ((2 * t : ℝ) : ℂ))) =
      (χ (n : ZMod 5) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) ^ 2 := by
  rw [χ.pow_apply' (by decide : 2 ≠ 0)]
  rw [show -(Complex.I * ((2 * t : ℝ) : ℂ)) =
      (2 : ℕ) * (-(Complex.I * (t : ℂ))) by push_cast; ring,
    Complex.cpow_nat_mul, mul_pow]

lemma modFive_mangoldt_term_positivity (χ : DirichletCharacter ℂ 5)
    (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n).re +
      4 * (LSeries.term (modFiveMangoldtTwist χ)
        ((σ : ℂ) + Complex.I * (t : ℂ)) n).re +
      (LSeries.term (modFiveMangoldtTwist (χ ^ 2))
        ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, Complex.zero_re, mul_zero, add_zero, le_refl]
  rw [modFive_real_mangoldt_term σ n hn,
    modFive_twisted_mangoldt_term χ σ t n hn,
    modFive_twisted_mangoldt_term (χ ^ 2) σ (2 * t) n hn,
    modFive_double_phase]
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hpoly := modFive_three_four_one_nonneg (modFive_twisted_phase_norm χ n hn t)
  simp only [Complex.mul_re] at hpoly
  have ha : 0 ≤ vonMangoldt n * (n : ℝ) ^ (-σ) :=
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _)
  nlinarith [mul_nonneg ha hpoly]

/-- Positivity of the three actual, absolutely convergent Mangoldt series. -/
theorem modFive_mangoldt_series_positivity (χ : DirichletCharacter ℂ 5)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (LSeries (fun m => (vonMangoldt m : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (modFiveMangoldtTwist χ) ((σ : ℂ) + Complex.I * (t : ℂ))).re +
      (LSeries (modFiveMangoldtTwist (χ ^ 2))
        ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re := by
  have hs0 : 1 < (σ : ℂ).re := hσ
  have hs1 : 1 < ((σ : ℂ) + Complex.I * (t : ℂ)).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)).re := by simpa using hσ
  have h0 := Complex.hasSum_re (LSeriesSummable_vonMangoldt hs0).LSeriesHasSum
  have h1 := Complex.hasSum_re (χ.LSeriesSummable_twist_vonMangoldt hs1).LSeriesHasSum
  have h2 := Complex.hasSum_re ((χ ^ 2).LSeriesSummable_twist_vonMangoldt hs2).LSeriesHasSum
  exact (((h0.mul_left 3).add (h1.mul_left 4)).add h2).nonneg
    (modFive_mangoldt_term_positivity χ σ t)

lemma modFive_twisted_series_logderiv (χ : DirichletCharacter ℂ 5)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (modFiveMangoldtTwist χ) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact χ.LSeries_twist_vonMangoldt_eq hs

/-- The fixed-character logarithmic-derivative inequality needed by the
quantitative zero-free-region proof. -/
theorem modFive_logderiv_positivity (χ : DirichletCharacter ℂ 5)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re +
      (-deriv (DirichletCharacter.LFunction (χ ^ 2))
        ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)) /
        DirichletCharacter.LFunction (χ ^ 2)
          ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re := by
  have h := modFive_mangoldt_series_positivity χ hσ t
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ,
    modFive_twisted_series_logderiv χ (by simpa using hσ),
    modFive_twisted_series_logderiv (χ ^ 2) (by simpa using hσ)] at h
  exact h

end TwoPointCorrelations

end OAI
