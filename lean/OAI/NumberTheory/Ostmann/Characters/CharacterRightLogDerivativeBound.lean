import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothRightContour

namespace OAI

/-! # A uniform logarithmic derivative bound to the right of two -/

namespace Ostmann

open Complex

/-- Absolute convergence supplies a single bound for every primitive character. -/
theorem character_logDeriv_right_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 2 ≤ s.re → ‖logDeriv χ.L s‖ ≤ C := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let C : ℝ := ∑' n, ‖LSeries.term f (2 : ℂ) n‖
  have hsum : LSeriesSummable f (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hC : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C + 1, by positivity, ?_⟩
  intro χ s hs
  have hcs : LSeriesSummable (characterMangoldtCoefficient χ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by linarith)
  have hterm (n : ℕ) : ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ ≤
      ‖LSeries.term f (2 : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    rw [show (2 : ℂ).re = (2 : ℝ) by norm_num]
    split_ifs with hn
    · exact le_rfl
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      apply div_le_div₀ (norm_nonneg _) _ (Real.rpow_pos_of_pos hnpos _)
        (Real.rpow_le_rpow_of_exponent_le hn1 hs)
      dsimp only [characterMangoldtCoefficient, f]
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.character.norm_le_one _)
  calc
    ‖logDeriv χ.L s‖ = ‖LSeries (characterMangoldtCoefficient χ) s‖ := by
      rw [χ.mangoldt_LSeries_eq s (by linarith), logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ :=
      norm_tsum_le_tsum_norm hcs.norm
    _ ≤ C := hcs.norm.tsum_le_tsum hterm hsum.norm
    _ ≤ C + 1 := by linarith

end Ostmann

end OAI
