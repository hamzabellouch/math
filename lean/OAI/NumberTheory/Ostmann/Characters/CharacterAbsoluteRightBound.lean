import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothDirichletIntegral
import OAI.NumberTheory.Ostmann.ZeroDensity.DirichletLogDerivativeBound

namespace OAI

/-! # Absolute Euler-series control on every right-hand vertical line -/

namespace Ostmann

open Complex LSeries
open scoped ComplexOrder

 theorem character_logDeriv_right_pole_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      ‖logDeriv χ.L s‖ ≤ 1 / (s.re - 1) + C := by
  obtain ⟨C, hC, hb⟩ := exists_vonMangoldt_series_bound
  refine ⟨C, hC, ?_⟩
  intro χ s hs hs2
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have ha : LSeriesSummable a (s.re : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have ht : LSeriesSummable (characterMangoldtCoefficient χ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character hs
  have hsame (n : ℕ) : ‖LSeries.term a s n‖ = ‖LSeries.term a (s.re : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq, Complex.ofReal_re]
  have hn (n : ℕ) : ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ ≤
      ‖LSeries.term a (s.re : ℂ) n‖ := by
    rw [← hsame n]
    apply LSeries.norm_term_le
    change ‖χ.character (n : ZMod χ.modulus) * a n‖ ≤ ‖a n‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.character.norm_le_one _)
  have hr (n : ℕ) : ‖LSeries.term a (s.re : ℂ) n‖ =
      (LSeries.term a (s.re : ℂ) n).re := by
    have hp : (0 : ℂ) ≤ a n := by
      change (0 : ℂ) ≤ (ArithmeticFunction.vonMangoldt n : ℂ)
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hh := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg hp s.re))
    simpa only [Complex.ofReal_re] using hh.symm
  calc
    _ = ‖LSeries (characterMangoldtCoefficient χ) s‖ := by
      rw [χ.mangoldt_LSeries_eq s hs, logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ := norm_tsum_le_tsum_norm ht.norm
    _ ≤ ∑' n, ‖LSeries.term a (s.re : ℂ) n‖ := ht.norm.tsum_le_tsum hn ha.norm
    _ = (LSeries a (s.re : ℂ)).re := by simp_rw [hr]; exact (Complex.re_tsum ha).symm
    _ ≤ ‖LSeries a (s.re : ℂ)‖ := Complex.re_le_norm _
    _ ≤ _ := hb s.re hs hs2

end Ostmann

end OAI
