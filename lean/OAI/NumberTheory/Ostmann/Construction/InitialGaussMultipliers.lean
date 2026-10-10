import OAI.NumberTheory.Ostmann.Construction.ConstituentInitialAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.SampledTupleAmplitude

namespace OAI

/-! # The actual bounded Gauss multipliers for every original prime role -/

namespace Ostmann
open scoped Classical

noncomputable def primeGaussMultiplier (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (p : ℕ) : ℂ :=
  if hp : p.Prime ∧ χ p ≠ 1 then
    @primitiveGaussPhase p ⟨hp.1.ne_zero⟩ (χ p) else 1

theorem primeGaussMultiplier_norm (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (p : ℕ) :
    ‖primeGaussMultiplier χ p‖ = 1 := by
  unfold primeGaussMultiplier
  split_ifs with hp
  · exact @primitiveGaussPhase_norm p ⟨hp.1.ne_zero⟩ _
      (prime_character_isPrimitive p hp.1 (χ p) hp.2)
  · exact norm_one

theorem primeGaussMultiplier_eq (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (p : ℕ) (hp : p.Prime) (hχ : χ p ≠ 1) :
    primeGaussMultiplier χ p = @primitiveGaussPhase p ⟨hp.ne_zero⟩ (χ p) := by
  unfold primeGaussMultiplier
  exact dite_eq_left (show p.Prime ∧ χ p ≠ 1 from ⟨hp, hχ⟩)

end Ostmann

end OAI
