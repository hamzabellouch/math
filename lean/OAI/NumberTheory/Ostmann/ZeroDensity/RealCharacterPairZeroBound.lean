import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterPairEuler
import OAI.NumberTheory.Ostmann.ZeroDensity.NonprincipalLogDerivative

namespace OAI

/-! # One zeta pole controls the two distinct real-character zero sums -/

namespace Ostmann

open Complex

theorem exists_distinct_real_zero_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ ψ : PrimitiveRealCharacter), χ ≠ ψ → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      shiftedRealCharacterZeroSum χ (σ : ℂ) + shiftedRealCharacterZeroSum ψ (σ : ℂ) ≤
        1 / (σ - 1) + 4 * (Real.log χ.modulus + Real.log ψ.modulus) + C := by
  obtain ⟨B, hB, hb⟩ := exists_nonprincipal_logDeriv_real_lower
  obtain ⟨G, hG, hg⟩ := exists_low_height_zero_sum_error
  obtain ⟨R, hR, hr⟩ := exists_vonMangoldt_series_bound
  refine ⟨R + B * Real.log 2 + 2 * G, by positivity, ?_⟩
  intro χ ψ hne σ hσ hσ2
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let : NeZero ψ.modulus := ⟨ψ.positive.ne'⟩
  let N := χ.modulus * ψ.modulus
  let : NeZero N := ⟨Nat.mul_ne_zero χ.positive.ne' ψ.positive.ne'⟩
  have hχN : χ.modulus ∣ N := Nat.dvd_mul_right _ _
  have hψN : ψ.modulus ∣ N := Nat.dvd_mul_left _ _
  let a := DirichletCharacter.changeLevel hχN χ.complexCharacter
  let b := DirichletCharacter.changeLevel hψN ψ.complexCharacter
  have hab : a * b ≠ 1 := distinct_real_lifts_product_nonprincipal χ ψ hne hχN hψN
  have hp := real_character_pair_logDeriv_le a b (χ.lift_inverse_eq hχN)
    (ψ.lift_inverse_eq hψN) σ hσ
  have hprod := hb N (a * b) hab (σ : ℂ) hσ hσ2
  simp only [Complex.ofReal_im, abs_zero, zero_add] at hprod
  have hvr := (Complex.re_le_norm _).trans (hr σ hσ hσ2)
  have hχdiff := logDeriv_changeLevel_bound χ.complexCharacter hχN (σ : ℂ) hσ
  have hψdiff := logDeriv_changeLevel_bound ψ.complexCharacter hψN (σ : ℂ) hσ
  have hχre := Complex.re_le_norm (-(logDeriv (DirichletCharacter.LFunction a) (σ : ℂ) - logDeriv χ.L (σ : ℂ)))
  have hψre := Complex.re_le_norm (-(logDeriv (DirichletCharacter.LFunction b) (σ : ℂ) - logDeriv ψ.L (σ : ℂ)))
  simp only [Complex.neg_re, Complex.sub_re, norm_neg] at hχre hψre
  have hx := hg χ (σ : ℂ) hσ hσ2 (by simp)
  have hy := hg ψ (σ : ℂ) hσ hσ2 (by simp)
  have hlog : Real.log N = Real.log χ.modulus + Real.log ψ.modulus := by
    rw [show (N : ℝ) = (χ.modulus : ℝ) * ψ.modulus by simp [N], Real.log_mul]
    · exact_mod_cast χ.positive.ne'
    · exact_mod_cast ψ.positive.ne'
  change ‖logDeriv (DirichletCharacter.LFunction a) (σ : ℂ) - logDeriv χ.L (σ : ℂ)‖ ≤ _ at hχdiff
  change ‖logDeriv (DirichletCharacter.LFunction b) (σ : ℂ) - logDeriv ψ.L (σ : ℂ)‖ ≤ _ at hψdiff
  rw [hlog] at hχdiff hψdiff hprod
  nlinarith

end Ostmann

end OAI
