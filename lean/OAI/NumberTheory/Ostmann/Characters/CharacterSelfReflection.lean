import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexCharacterConjugation

namespace OAI

/-! # The zero-copy permutation across the critical line -/

namespace Ostmann

open Complex
open scoped ComplexConjugate Classical

theorem PrimitiveComplexCharacter.zero_self_reflection (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : z ∈ complexCharacterZeros χ) : 1 - conj z ∈ complexCharacterZeros χ := by
  refine ⟨by simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith [hz.2.1],
    by simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith [hz.1], ?_⟩
  have hn := (χ.L_analytic z).analyticOrderAt_ne_zero.mpr hz.2.2
  rw [← χ.L_order_self_reflection z hz.1 hz.2.1] at hn
  exact (χ.L_analytic (1 - conj z)).analyticOrderAt_ne_zero.mp hn

noncomputable def characterZeroCopySelfReflection (χ : PrimitiveComplexCharacter) :
    CharacterZeroCopy χ ≃ CharacterZeroCopy χ := by
  let f : CharacterZeroCopy χ → CharacterZeroCopy χ := fun c =>
    ⟨(1 - conj c.val.1, c.val.2), χ.zero_self_reflection c.val.1 c.property.1, by
      unfold analyticOrderNatAt
      rw [χ.L_order_self_reflection _ c.property.1.1 c.property.1.2.1]
      exact c.property.2⟩
  apply Function.Involutive.toPerm (f := f)
  intro c
  apply Subtype.ext
  apply Prod.ext
  · change 1 - conj (1 - conj c.val.1) = c.val.1
    simp
  · rfl

noncomputable def characterZeroIndexSelfReflection (χ : PrimitiveComplexCharacter) : ℕ ≃ ℕ :=
  (faithfulCharacterZeroEquiv χ).trans
    ((characterZeroCopySelfReflection χ).trans (faithfulCharacterZeroEquiv χ).symm)

theorem characterZeroIndexSelfReflection_zeros (χ : PrimitiveComplexCharacter) (i : ℕ) :
    (actualCharacterZeros χ).zeros (characterZeroIndexSelfReflection χ i) =
      1 - conj ((actualCharacterZeros χ).zeros i) := by
  simp [actualCharacterZeros, characterZeroEnumeration,
    characterZeroIndexSelfReflection, characterZeroCopySelfReflection, Function.Involutive.toPerm]

end Ostmann

end OAI
