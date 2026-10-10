import OAI.NumberTheory.TwoPointCorrelations.ModFivePerronShift
import OAI.NumberTheory.TwoPointCorrelations.ModFiveSmoothedPsi

namespace OAI

/-! Absolute convergence bounds on the right Perron line.  The twisted
series is dominated term by term by the untwisted Mangoldt series, whose
pole bound controls the series uniformly. -/

namespace TwoPointCorrelations

open Complex ArithmeticFunction Erdos970
open scoped BigOperators

lemma modFive_mangoldt_norm (χ : DirichletCharacter ℂ 5) (n : ℕ) :
    ‖modFiveMangoldtTwist χ n‖ ≤ ‖(vonMangoldt n : ℂ)‖ := by
  unfold modFiveMangoldtTwist
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans_eq
    (one_mul _)

lemma modFive_logderiv_right_domination (χ : DirichletCharacter ℂ 5)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ‖-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs : 1 < s.re := by simpa [s] using hσ
  have hsum := χ.LSeriesSummable_twist_vonMangoldt hs
  have hsum0 := LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ
  have hterm (n : ℕ) : ‖LSeries.term (modFiveMangoldtTwist χ) s n‖ ≤
      ‖LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n‖ := by
    have he : ‖LSeries.term (modFiveMangoldtTwist χ) s n‖ =
        ‖LSeries.term (modFiveMangoldtTwist χ) (σ : ℂ) n‖ := by
      simp only [LSeries.norm_term_eq, s, add_re, ofReal_re, mul_I_re, ofReal_im,
        neg_zero, add_zero]
    rw [he]
    exact LSeries.norm_term_le _ (modFive_mangoldt_norm χ n)
  have heq : (∑' n, ‖LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n‖) =
      ‖-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    rw [helper_norm_neg_logDeriv_eq_tsum_norm σ hσ]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · rw [LSeries.term_of_ne_zero hn]
  rw [← modFive_twisted_series_logderiv χ hs]
  change ‖∑' n, LSeries.term (modFiveMangoldtTwist χ) s n‖ ≤ _
  exact (norm_tsum_le_tsum_norm hsum.norm).trans
    ((hsum.norm.tsum_le_tsum hterm hsum0.norm).trans_eq heq)

/-- A uniform right-line bound, valid for every character, with only the
explicit simple-pole dependence on the distance from one. -/
theorem modFive_logderiv_right_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5) (δ t : ℝ), 0 < δ →
      ‖-deriv (DirichletCharacter.LFunction χ) (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          1 / δ + C := by
  obtain ⟨C, hC, hbound⟩ := Z0bound_const
  refine ⟨C, lt_trans zero_lt_one hC, ?_⟩
  intro χ δ t hδ
  have hmain := modFive_logderiv_right_domination χ (by linarith : 1 < 1 + δ) t
  have hz := hbound δ hδ
  have hz' : ‖-deriv riemannZeta (((1 + δ : ℝ) : ℂ)) /
      riemannZeta (((1 + δ : ℝ) : ℂ)) - 1 / (δ : ℂ)‖ ≤ C := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one, logDerivZeta, neg_div] using hz
  have hn : ‖(1 : ℂ) / (δ : ℂ)‖ = 1 / δ := by
    simp [abs_of_pos hδ]
  have hb := norm_le_insert' (-deriv riemannZeta (((1 + δ : ℝ) : ℂ)) /
      riemannZeta (((1 + δ : ℝ) : ℂ))) (1 / (δ : ℂ))
  exact hmain.trans (hb.trans (by rw [hn]; linarith))

end TwoPointCorrelations

end OAI
