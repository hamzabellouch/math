import OAI.NumberTheory.Ostmann.ZeroDensity.GammaFactorialGrowth
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaGrowth

namespace OAI

/-! # Factorial growth for the archimedean factors on expanding disks -/

namespace Ostmann

open Complex

theorem gammaReal_factorial_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (s : ℂ), (1 / 2 : ℝ) ≤ s.re → s.re ≤ (N : ℝ) + 2 →
      ‖Complex.Gammaℝ s‖ ≤ C + ((N + 1).factorial : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := gamma_factorial_growth
  refine ⟨C, hC, ?_⟩
  intro N s hs hs'
  have hg := hbound N (s / 2) (by simp; linarith) (by simp; linarith [Nat.cast_nonneg (α := ℝ) N])
  have hp : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
    simp
    linarith
  rw [Complex.Gammaℝ_def, norm_mul]
  exact (mul_le_mul hp hg (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem characterGamma_factorial_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (N : ℕ) (s : ℂ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ (N : ℝ) + 1 →
      ‖DirichletCharacter.gammaFactor χ.character s‖ ≤ C + ((N + 1).factorial : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := gammaReal_factorial_growth
  refine ⟨C, hC, ?_⟩
  intro χ N s hs hs'
  classical
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact hbound N s hs (by linarith)
  · exact hbound N (s + 1) (by simp; linarith) (by simp; linarith)

end Ostmann

end OAI
