import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveRieszComparison
import OAI.NumberTheory.Ostmann.Characters.PrimitiveCharacterLifts

namespace OAI

/-! # The primitive label of a lifted primitive character -/

namespace Ostmann

theorem primitiveCharacterReduction_lift (q : ℕ) [NeZero q]
    (ρ : PrimitiveComplexCharacter) (hd : ρ.modulus ∣ q) :
    primitiveCharacterReduction (DirichletCharacter.changeLevel hd ρ.character) = some ρ := by
  let χ := DirichletCharacter.changeLevel hd ρ.character
  have hne : χ ≠ 1 := by
    change DirichletCharacter.changeLevel hd ρ.character ≠ 1
    exact mt (DirichletCharacter.changeLevel_eq_one_iff hd).mp ρ.nontrivial
  cases he : primitiveCharacterReduction χ with
  | none =>
    have hh := lift_primitiveCharacterReduction χ
    rw [he] at hh
    exact (hne hh.symm).elim
  | some τ =>
    have hτ := primitiveReduction_divides χ τ he
    have hh := lift_primitiveCharacterReduction χ
    rw [he] at hh
    simp only [liftPrimitiveCharacter, dite_eq_left hτ] at hh
    have hτρ : τ = ρ := τ.eq_of_changeLevel_eq ρ hτ hd hh
    simp only [hτρ]

theorem primitiveCharacterReduction_eq_some_iff (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : PrimitiveComplexCharacter) (hd : ρ.modulus ∣ q) :
    primitiveCharacterReduction χ = some ρ ↔
      χ = DirichletCharacter.changeLevel hd ρ.character := by
  constructor
  · intro he
    have hh := lift_primitiveCharacterReduction χ
    rw [he] at hh
    simpa only [liftPrimitiveCharacter, dite_eq_left hd] using hh.symm
  · rintro rfl
    exact primitiveCharacterReduction_lift q ρ hd

theorem primitiveCharacterReduction_eq_none_iff (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) : primitiveCharacterReduction χ = none ↔ χ = 1 := by
  constructor
  · intro he
    have hh := lift_primitiveCharacterReduction χ
    rw [he] at hh
    exact hh.symm
  · intro he
    simp [primitiveCharacterReduction, he]

end Ostmann

end OAI
