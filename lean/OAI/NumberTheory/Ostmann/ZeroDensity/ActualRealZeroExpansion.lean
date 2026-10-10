import OAI.NumberTheory.Ostmann.ZeroDensity.RealCompletedHadamard
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaRealBound

namespace OAI

/-! # The actual real-character Hadamard expansion -/

namespace Ostmann

open Complex

noncomputable def actualRealZeroErrorConstant : ℝ := Classical.choose characterGamma_real_logDeriv_bound

theorem actualRealZeroErrorConstant_pos : 0 < actualRealZeroErrorConstant :=
  (Classical.choose_spec characterGamma_real_logDeriv_bound).1

/-- The exact zero-sum identity has only the bounded archimedean term left over. -/
theorem real_character_hadamard_error (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 1 < s) (hs2 : s ≤ 2) :
    |realCharacterZeroSum χ s - χ.logDerivative s - (1 / 2) * Real.log χ.modulus| ≤
      actualRealZeroErrorConstant := by
  have he : realCharacterZeroSum χ s - χ.logDerivative s - (1 / 2) * Real.log χ.modulus =
      (logDeriv (DirichletCharacter.gammaFactor χ.complexCharacter) (s : ℂ)).re := by
    rw [real_completed_hadamard_identity χ s hs hs2,
      χ.asComplex.completed_logDeriv_eq_add (s : ℂ) (by simp; linarith)]
    rw [PrimitiveRealCharacter.asComplex_L]
    change (logDeriv χ.L (s : ℂ) +
      logDeriv (DirichletCharacter.gammaFactor χ.complexCharacter) (s : ℂ)).re +
      (1 / 2) * Real.log χ.modulus - χ.logDerivative s -
      (1 / 2) * Real.log χ.modulus = _
    simp only [Complex.add_re, PrimitiveRealCharacter.logDerivative, logDeriv_apply]
    ring
  rw [he]
  exact (abs_re_le_norm _).trans
    ((Classical.choose_spec characterGamma_real_logDeriv_bound).2 χ.asComplex s hs hs2)

/-- The Hadamard expansion fields of the real-zero input. -/
noncomputable def actualRealCharacterZeroExpansion (χ : PrimitiveRealCharacter) :
    RealCharacterZeroExpansion χ actualRealZeroErrorConstant where
  zeros := (realCharacterActualZeros χ).zeros
  in_strip := (realCharacterActualZeros χ).in_strip
  actual_zero := (realCharacterActualZeros χ).actual_zero
  summable := real_character_zero_kernel_summable χ
  hadamard := real_character_hadamard_error χ

/-- The low-height clause of Montgomery--Vaughan 11.3/11.10,
stated for the analytic multiplicity enumeration. -/
def ActualRealLowHeightRegion (P : PublishedProgressionInput) : Prop :=
  ∀ (χ : PrimitiveRealCharacter) (Q : ℕ), 2 ≤ Q → χ.modulus ≤ Q →
    ∃ E : Finset ℕ, E.card ≤ 1 ∧
      (∀ i ∈ E, ((realCharacterActualZeros χ).zeros i).im = 0 ∧
        1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ ((realCharacterActualZeros χ).zeros i).re) ∧
      (∀ i ∉ E, ((realCharacterActualZeros χ).zeros i).im ^ 2 < 1 →
        ((realCharacterActualZeros χ).zeros i).re ≤ 1 - P.kappa / Real.log (4 * (Q : ℝ)))

noncomputable def actualPublishedRealZeroInput (P : PublishedProgressionInput)
    (hregion : ActualRealLowHeightRegion P) : PublishedRealZeroInput P where
  errorConstant := actualRealZeroErrorConstant
  errorConstant_nonneg := actualRealZeroErrorConstant_pos.le
  expansion := actualRealCharacterZeroExpansion
  region := hregion

end Ostmann

end OAI
