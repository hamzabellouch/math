import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothDirichletIntegral

namespace OAI

/-! # The absolutely convergent logarithmic derivative on Re(s)=3/2 -/

namespace Ostmann

open scoped BigOperators

theorem character_logDeriv_right_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), s.re = 3 / 2 → ‖logDeriv χ.L s‖ ≤ C := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let C : ℝ := ∑' n, ‖LSeries.term f (3 / 2 : ℂ) n‖
  have hsum : LSeriesSummable f (3 / 2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hC : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C + 1, by positivity, ?_⟩
  intro χ s hs
  have hcs : LSeriesSummable (characterMangoldtCoefficient χ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by rw [hs]; norm_num)
  have hterm (n : ℕ) : ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ ≤
      ‖LSeries.term f (3 / 2 : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]
    rw [show (3 / 2 : ℂ).re = (3 / 2 : ℝ) by norm_num]
    split_ifs with hn
    · exact le_rfl
    · apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      dsimp only [characterMangoldtCoefficient, f]
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.character.norm_le_one _)
  calc
    ‖logDeriv χ.L s‖ = ‖LSeries (characterMangoldtCoefficient χ) s‖ := by
      rw [χ.mangoldt_LSeries_eq s (by rw [hs]; norm_num), logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ :=
      norm_tsum_le_tsum_norm hcs.norm
    _ ≤ C := hcs.norm.tsum_le_tsum hterm hsum.norm
    _ ≤ C + 1 := by linarith

end Ostmann

end OAI
