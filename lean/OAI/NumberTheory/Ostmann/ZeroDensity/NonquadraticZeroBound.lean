import OAI.NumberTheory.Ostmann.ZeroDensity.NonprincipalLogDerivative
import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexCharacterTrigonometric

namespace OAI

/-! # The full-height zero-sum bound when the squared character is nonprincipal -/

namespace Ostmann

open Complex

theorem log_double_abs_height_le (t : ℝ) :
    Real.log (|2 * t| + 2) ≤ 2 * Real.log (|t| + 2) := by
  have ht : 0 ≤ |t| := abs_nonneg t
  have hl : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  calc
    Real.log (|2 * t| + 2) ≤ Real.log (2 * (|t| + 2)) := by
      apply Real.log_le_log (by positivity)
      rw [abs_mul]
      norm_num
      linarith
    _ = Real.log 2 + Real.log (|t| + 2) := Real.log_mul (by norm_num) (by positivity)
    _ ≤ 2 * Real.log (|t| + 2) := by linarith

theorem exists_nonquadratic_zero_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter), χ.character ^ 2 ≠ 1 →
      ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
        4 * characterRealZeroSum χ ((σ : ℂ) + (t : ℂ) * I) ≤
          3 / (σ - 1) + C * (Real.log χ.modulus + Real.log (|t| + 2) + 1) := by
  obtain ⟨B, hB, hb⟩ := exists_nonprincipal_logDeriv_real_lower
  obtain ⟨G, hG, hg⟩ := exists_character_zero_sum_log_bound
  obtain ⟨V, hV, hv⟩ := exists_vonMangoldt_series_bound
  refine ⟨4 * G + 2 * B + 4 * V + 4, by positivity, ?_⟩
  intro χ hχ σ t hσ hσ2
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hp := complex_character_trigonometric_sum_nonneg χ.character σ t hσ
  rw [dirichlet_mangoldt_LSeries_eq _ _ (by simpa using hσ),
    dirichlet_mangoldt_LSeries_eq _ _ (by simpa using hσ), Complex.neg_re, Complex.neg_re] at hp
  have hh := hg χ ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ) (by simpa using hσ2)
  have hd := hb χ.modulus (χ.character ^ 2) hχ
    ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) (by simpa using hσ) (by simpa using hσ2)
  have hvr := (Complex.re_le_norm _).trans (hv σ hσ hσ2)
  have hlog := log_double_abs_height_le t
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
    Complex.ofReal_re, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hh hd
  change 4 * characterRealZeroSum χ _ ≤ _
  change characterRealZeroSum χ _ ≤
    (logDeriv (DirichletCharacter.LFunction χ.character) _).re +
      (1 / 2) * Real.log χ.modulus + G * Real.log (|t| + 2) at hh
  have hBlog := mul_le_mul_of_nonneg_left hlog hB.le
  have hGq := mul_nonneg hG.le hq
  have hBq := mul_nonneg hB.le hq
  have hVq := mul_nonneg hV.le hq
  have hVt := mul_nonneg hV.le ht
  simp only [div_eq_mul_inv] at hvr ⊢
  nlinarith

end Ostmann

end OAI
