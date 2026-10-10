import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySmoothedKernel
import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySquareSeries

namespace OAI

/-! # Absolutely integrable Dirichlet terms on the initial right line -/

namespace Ostmann

open Complex MeasureTheory

noncomputable def densitySquareCoefficient (χ : PrimitiveComplexCharacter) (n : ℕ) : ℂ :=
  χ.character (n : ZMod χ.modulus) * (n.divisors.card : ℂ)

 theorem densitySquareCoefficient_summable (χ : PrimitiveComplexCharacter) :
    LSeriesSummable (densitySquareCoefficient χ) (3 / 2 : ℂ) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have h := (χ.character.LSeriesSummable_of_one_lt_re (s := (3 / 2 : ℂ)) (by norm_num)).convolution
    (χ.character.LSeriesSummable_of_one_lt_re (s := (3 / 2 : ℂ)) (by norm_num))
  rw [density_character_self_convolution] at h
  exact h

noncomputable def densitySquareSeriesTerm (χ : PrimitiveComplexCharacter) (s : ℂ)
    (n : ℕ) (u : ℝ) : ℂ :=
  densitySquareKernel χ s (1 + u * I) *
    LSeries.term (densitySquareCoefficient χ) (s + (1 + u * I)) n

 theorem densitySquareSeriesTerm_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (n : ℕ) (u : ℝ) :
    ‖densitySquareSeriesTerm χ s n u‖ ≤
      ((Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2))) *
        ‖LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n‖) *
          Real.exp (-(u ^ 2) / 2) := by
  have he : ‖LSeries.term (densitySquareCoefficient χ) (s + (1 + (u : ℂ) * I)) n‖ =
      ‖LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    norm_num [hs]
  rw [densitySquareSeriesTerm, norm_mul, he]
  have h := mul_le_mul_of_nonneg_right (densitySquareKernel_line_bound χ s hs u)
    (norm_nonneg (LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n))
  convert h using 1
  ring

 theorem densitySquareSeriesTerm_continuous (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (n : ℕ) : Continuous (densitySquareSeriesTerm χ s n) := by
  apply (densitySquareKernel_line_continuous χ s hs).mul
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hp : Continuous (fun u : ℝ => (n : ℂ) ^ (s + (1 + u * I))) :=
      (differentiable_id.const_cpow (Or.inl hnC)).continuous.comp (by fun_prop)
    exact continuous_const.div hp (fun u => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))

 theorem densitySquareSeriesTerm_integrable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (n : ℕ) : Integrable (densitySquareSeriesTerm χ s n) := by
  have hg : Integrable (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) := by
    convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
    funext u
    congr 1
    ring
  apply (hg.const_mul ((Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2))) *
        ‖LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n‖)).mono'
    (densitySquareSeriesTerm_continuous χ s hs n).aestronglyMeasurable
  filter_upwards with u
  exact densitySquareSeriesTerm_bound χ s hs n u

end Ostmann

end OAI
