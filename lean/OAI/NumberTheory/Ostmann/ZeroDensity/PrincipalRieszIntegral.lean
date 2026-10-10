import OAI.NumberTheory.Ostmann.ZeroDensity.RieszVerticalWeight
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothDirichletIntegral

namespace OAI

/-! # The exact starting contour for the principal Riesz mean -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

noncomputable def principalMangoldtCoefficient (n : ℕ) : ℂ := ArithmeticFunction.vonMangoldt n

theorem principalMangoldt_riesz_term_norm (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term principalMangoldtCoefficient (rieszMellinLine σ t) n‖ =
      ‖LSeries.term principalMangoldtCoefficient (σ : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

theorem principalMangoldt_riesz_term_continuous (σ : ℝ) (n : ℕ) :
    Continuous (fun t => LSeries.term principalMangoldtCoefficient (rieszMellinLine σ t) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    exact continuous_const.div ((rieszMellinLine_continuous σ).const_cpow
      (.inl (by exact_mod_cast hn))) (fun _ => Complex.cpow_ne_zero_iff.mpr
        (.inl (by exact_mod_cast hn)))

noncomputable def principalRieszMean (X : ℝ) : ℂ :=
  ∑' n : ℕ, principalMangoldtCoefficient n * rieszPrimeTest (n / X)

noncomputable def principalRieszVerticalTerm
    (X σ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (principalMangoldtCoefficient) (rieszMellinLine σ t) n *
    rieszVerticalWeight X σ t

theorem principalRieszVerticalTerm_norm
    (X σ : ℝ) (n : ℕ) (t : ℝ) :
    ‖principalRieszVerticalTerm X σ n t‖ =
      ‖LSeries.term (principalMangoldtCoefficient) (σ : ℂ) n‖ *
        ‖rieszVerticalWeight X σ t‖ := by
  rw [principalRieszVerticalTerm, norm_mul, principalMangoldt_riesz_term_norm]

theorem principalRieszVerticalTerm_integrable
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) (n : ℕ) :
    Integrable (principalRieszVerticalTerm X σ n) := by
  apply ((rieszVerticalWeight_integrable X σ hX hσ).norm.const_mul
    ‖LSeries.term (principalMangoldtCoefficient) (σ : ℂ) n‖).mono'
  · exact ((principalMangoldt_riesz_term_continuous σ n).mul
      (rieszVerticalWeight_continuous X σ hX (by linarith))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => (principalRieszVerticalTerm_norm X σ n t).le)

theorem principalRieszVerticalTerm_summable_norm
    (X σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n => ∫ t : ℝ, ‖principalRieszVerticalTerm X σ n t‖) := by
  have hsum : LSeriesSummable (principalMangoldtCoefficient) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hs := hsum.norm.mul_right (∫ t : ℝ, ‖rieszVerticalWeight X σ t‖)
  apply hs.congr
  intro n
  simp only [principalRieszVerticalTerm_norm, integral_const_mul]

theorem principalMangoldt_riesz_term_inversion
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, principalRieszVerticalTerm X σ n t) =
      principalMangoldtCoefficient n * rieszPrimeTest (n / X) := by
  by_cases hn : n = 0
  · subst n
    simp [principalRieszVerticalTerm, principalMangoldtCoefficient]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hkernel (t : ℝ) : principalRieszVerticalTerm X σ n t =
      principalMangoldtCoefficient n *
        (((n : ℝ) / X : ℝ) : ℂ) ^ (-rieszMellinLine σ t) *
          rieszMellinKernel (rieszMellinLine σ t) := by
    rw [principalRieszVerticalTerm, LSeries.term_of_ne_zero hn, rieszVerticalWeight,
      Complex.cpow_neg, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg hnR.le hX.le, inv_div]
    push_cast
    ring
  simp_rw [hkernel, mul_assoc]
  rw [integral_const_mul]
  have hinv := rieszPrimeTest_mellin_inversion σ ((n : ℝ) / X) hσ (div_pos hnR hX)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
    (((n : ℝ) / X : ℝ) : ℂ) ^ (-rieszMellinLine σ t) *
      rieszMellinKernel (rieszMellinLine σ t)) = _ at hinv
  rw [← hinv]
  ring

theorem principalRieszMean_eq_vertical_logDerivative
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 < σ) :
    principalRieszMean X =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (-logDeriv riemannZeta (rieszMellinLine σ t)) * rieszVerticalWeight X σ t := by
  unfold principalRieszMean
  calc
    _ = ∑' n : ℕ, ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, principalRieszVerticalTerm X σ n t :=
      tsum_congr (fun n => (principalMangoldt_riesz_term_inversion X σ hX hσ.le n).symm)
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∑' n : ℕ, ∫ t : ℝ, principalRieszVerticalTerm X σ n t := tsum_mul_left
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, ∑' n : ℕ, principalRieszVerticalTerm X σ n t := by
      rw [integral_tsum_of_summable_integral_norm
        (principalRieszVerticalTerm_integrable X σ hX hσ.le)
        (principalRieszVerticalTerm_summable_norm X σ hσ)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [show (∑' n : ℕ, principalRieszVerticalTerm X σ n t) =
        LSeries (principalMangoldtCoefficient) (rieszMellinLine σ t) * rieszVerticalWeight X σ t from tsum_mul_right]
      have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (s := rieszMellinLine σ t) (by simpa using hσ)
      have he' : LSeries principalMangoldtCoefficient (rieszMellinLine σ t) =
          -logDeriv riemannZeta (rieszMellinLine σ t) := by
        change LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) _ = _
        simpa only [logDeriv_apply, neg_div] using he
      rw [he']

end Ostmann

end OAI
