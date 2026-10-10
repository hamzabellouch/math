import Mathlib.Basic.Denumerable
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZerosInfinite
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroCopies

namespace OAI

/-! # A faithful enumeration of all actual zeros with their multiplicities -/

namespace Ostmann

open Set
open scoped Classical

theorem characterZeroCopy_countable (χ : PrimitiveComplexCharacter) :
    Countable (CharacterZeroCopy χ) := by
  let : Countable (complexCharacterZeros χ) := χ.zeros_countable.to_subtype
  let f : CharacterZeroCopy χ → (complexCharacterZeros χ) × ℕ :=
    fun c => (⟨c.val.1, c.property.1⟩, c.val.2)
  apply Function.Injective.countable (f := f)
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z : (complexCharacterZeros χ) × ℕ => z.2) h)

theorem characterZeroCopy_infinite (χ : PrimitiveComplexCharacter) :
    Infinite (CharacterZeroCopy χ) := by
  let : Infinite (complexCharacterZeros χ) := χ.zeros_infinite.to_subtype
  let f : (complexCharacterZeros χ) → CharacterZeroCopy χ := fun z =>
    ⟨(z.val, 0), z.property, by
      have hh := (characterZeroOrder_pos_iff χ z.val).mpr z.property.2.2
      rwa [characterZeroOrder_eq_nat, Int.natCast_pos] at hh⟩
  apply Infinite.of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : CharacterZeroCopy χ => z.val.1) h

/-- No dummy zeros, repetitions, or omitted multiplicity labels occur. -/
noncomputable def faithfulCharacterZeroEquiv (χ : PrimitiveComplexCharacter) :
    ℕ ≃ CharacterZeroCopy χ := by
  letI := characterZeroCopy_countable χ
  letI := characterZeroCopy_infinite χ
  exact Classical.choice (inferInstance : Nonempty (ℕ ≃ CharacterZeroCopy χ))

noncomputable def actualCharacterZeros (χ : PrimitiveComplexCharacter) :
    ComplexZeroEnumeration χ := characterZeroEnumeration χ (faithfulCharacterZeroEquiv χ)

theorem actualCharacterZeros_respectsMultiplicity (χ : PrimitiveComplexCharacter) :
    (actualCharacterZeros χ).RespectsMultiplicity :=
  characterZeroEnumeration_respectsMultiplicity χ (faithfulCharacterZeroEquiv χ)

end Ostmann

end OAI
