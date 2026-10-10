import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterReflection

namespace OAI

/-! # Reflection as an actual permutation of all zero multiplicity labels -/

namespace Ostmann

open scoped Classical

theorem PrimitiveRealCharacter.zero_reflection (χ : PrimitiveRealCharacter)
    (z : ℂ) (hz : z ∈ complexCharacterZeros χ.asComplex) :
    1 - z ∈ complexCharacterZeros χ.asComplex := by
  refine ⟨by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.2.1],
    by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1], ?_⟩
  have hh := (characterZeroOrder_pos_iff χ.asComplex z).mpr hz.2.2
  rw [characterZeroOrder_eq_nat, Int.natCast_pos] at hh
  have hr := χ.zero_reflection_order z hz.1 hz.2.1
  apply (characterZeroOrder_pos_iff χ.asComplex (1 - z)).mp
  rw [characterZeroOrder_eq_nat, Int.natCast_pos]
  change 0 < analyticOrderNatAt χ.L (1 - z)
  rw [hr]
  exact hh

noncomputable def realZeroCopyReflection (χ : PrimitiveRealCharacter) :
    CharacterZeroCopy χ.asComplex ≃ CharacterZeroCopy χ.asComplex := by
  let f : CharacterZeroCopy χ.asComplex → CharacterZeroCopy χ.asComplex := fun c =>
    ⟨(1 - c.val.1, c.val.2), χ.zero_reflection c.val.1 c.property.1, by
      change c.val.2 < analyticOrderNatAt χ.L (1 - c.val.1)
      rw [χ.zero_reflection_order _ c.property.1.1 c.property.1.2.1]
      exact c.property.2⟩
  apply Function.Involutive.toPerm (f := f)
  intro c
  apply Subtype.ext
  apply Prod.ext
  · change 1 - (1 - c.val.1) = c.val.1
    ring
  · rfl

noncomputable def realZeroIndexReflection (χ : PrimitiveRealCharacter) : ℕ ≃ ℕ :=
  (faithfulCharacterZeroEquiv χ.asComplex).trans
    ((realZeroCopyReflection χ).trans (faithfulCharacterZeroEquiv χ.asComplex).symm)

theorem realZeroIndexReflection_zeros (χ : PrimitiveRealCharacter) (i : ℕ) :
    (realCharacterActualZeros χ).zeros (realZeroIndexReflection χ i) =
      1 - (realCharacterActualZeros χ).zeros i := by
  simp [realCharacterActualZeros, actualCharacterZeros, characterZeroEnumeration,
    realZeroIndexReflection, realZeroCopyReflection, Function.Involutive.toPerm]
  rfl

end Ostmann

end OAI
