import OAI.NumberTheory.Ostmann.Characters.CharacterAbsoluteRightBound

namespace OAI

/-! # Absolute zeta logarithmic-derivative control on right vertical lines -/

namespace Ostmann

open Complex LSeries
open scoped ComplexOrder

theorem zeta_logDeriv_right_pole_bound : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → ‖logDeriv riemannZeta s‖ ≤ 1 / (s.re - 1) + C := by
  obtain ⟨C, hC, hb⟩ := exists_vonMangoldt_series_bound
  refine ⟨C, hC, ?_⟩
  intro s hs hs2
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have ha : LSeriesSummable a (s.re : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have ht : LSeriesSummable a s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hn (n : ℕ) : ‖LSeries.term a s n‖ = ‖LSeries.term a (s.re : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq, Complex.ofReal_re]
  have hr (n : ℕ) : ‖LSeries.term a (s.re : ℂ) n‖ = (LSeries.term a (s.re : ℂ) n).re := by
    have hp : (0 : ℂ) ≤ a n := by
      change (0 : ℂ) ≤ (ArithmeticFunction.vonMangoldt n : ℂ)
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hh := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg hp s.re))
    simpa only [Complex.ofReal_re] using hh.symm
  have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change LSeries a s = _ at he
  calc
    _ = ‖LSeries a s‖ := by rw [he, logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term a s n‖ := norm_tsum_le_tsum_norm ht.norm
    _ = ∑' n, ‖LSeries.term a (s.re : ℂ) n‖ := tsum_congr hn
    _ = (LSeries a (s.re : ℂ)).re := by simp_rw [hr]; exact (Complex.re_tsum ha).symm
    _ ≤ ‖LSeries a (s.re : ℂ)‖ := Complex.re_le_norm _
    _ ≤ _ := hb s.re hs hs2

end Ostmann

end OAI
