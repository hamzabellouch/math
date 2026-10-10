import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedRealZeros
import OAI.NumberTheory.Ostmann.Characters.CharacterFaithfulEnumeration

namespace OAI

/-! # Real characters inside the actual complex-character zero development -/

namespace Ostmann

open scoped Classical

theorem PrimitiveRealCharacter.complex_factorsThrough_iff
    (χ : PrimitiveRealCharacter) (d : ℕ) :
    χ.complexCharacter.FactorsThrough d ↔ χ.character.FactorsThrough d := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  by_cases hd : d ∣ χ.modulus
  · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    constructor <;> intro h x hx
    · have hh := h hx
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hh ⊢
      simpa [PrimitiveRealCharacter.complexCharacter] using hh
    · have hh := h hx
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hh ⊢
      simp [PrimitiveRealCharacter.complexCharacter, hh]
  · constructor <;> intro h <;> exact (hd h.dvd).elim

theorem PrimitiveRealCharacter.complex_conductor (χ : PrimitiveRealCharacter) :
    χ.complexCharacter.conductor = χ.character.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  exact χ.complex_factorsThrough_iff d

/-- The coercion to complex values preserves the actual conductor and character. -/
noncomputable def PrimitiveRealCharacter.asComplex (χ : PrimitiveRealCharacter) :
    PrimitiveComplexCharacter where
  modulus := χ.modulus
  positive := χ.positive
  character := χ.complexCharacter
  primitive := by
    rw [DirichletCharacter.isPrimitive_def, χ.complex_conductor]
    exact χ.primitive
  nontrivial := (MulChar.ringHomComp_ne_one_iff Complex.ofReal_injective).mpr χ.nontrivial

@[simp] theorem PrimitiveRealCharacter.asComplex_L (χ : PrimitiveRealCharacter) :
    χ.asComplex.L = χ.L := rfl

noncomputable def realCharacterActualZeros (χ : PrimitiveRealCharacter) :
    ComplexZeroEnumeration χ.asComplex := actualCharacterZeros χ.asComplex

end Ostmann

end OAI
