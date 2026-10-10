import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterRieszZeroSelection
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualLocalZeros

namespace OAI

/-! # An actual indexed real zero as the canonical Page-zero datum -/

namespace Ostmann

noncomputable def indexedRealZero (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0) :
    PrimitiveRealZero where
  modulus := χ.modulus
  positive := χ.positive
  character := (χ.asReal hsq).character
  primitive := (χ.asReal hsq).primitive
  nontrivial := (χ.asReal hsq).nontrivial
  beta := ((actualCharacterZeros χ).zeros i).re
  beta_pos := ((actualCharacterZeros χ).in_strip i).1
  beta_lt_one := ((actualCharacterZeros χ).in_strip i).2
  zero := by
    change (χ.asReal hsq).asComplex.L (((actualCharacterZeros χ).zeros i).re : ℂ) = 0
    rw [χ.asReal_asComplex hsq]
    have he : (((actualCharacterZeros χ).zeros i).re : ℂ) = (actualCharacterZeros χ).zeros i := by
      apply Complex.ext <;> simp [him]
    rw [he]
    exact (actualCharacterZeros χ).actual_zero i

@[simp] theorem indexedRealZero_modulus (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0) :
    (indexedRealZero χ i hsq him).modulus = χ.modulus := rfl

@[simp] theorem indexedRealZero_beta (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0) :
    (indexedRealZero χ i hsq him).beta = ((actualCharacterZeros χ).zeros i).re := rfl

@[simp] theorem indexedRealZero_character (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0) :
    (indexedRealZero χ i hsq him).asRealCharacter.asComplex = χ := χ.asReal_asComplex hsq

theorem indexedRealZero_canonical (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0)
    (q : ℕ) (hq : 1 ≤ q) (hdvd : χ.modulus ∣ q)
    (hnear : 1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤
      ((actualCharacterZeros χ).zeros i).re) :
    actualLocalZero q = some (indexedRealZero χ i hsq him) :=
  actualLocalZero_complete q hq _ hdvd hnear

end Ostmann

end OAI
