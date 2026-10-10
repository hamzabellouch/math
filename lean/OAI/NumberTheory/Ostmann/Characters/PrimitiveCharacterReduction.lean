import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveCharacterCard

namespace OAI

/-! # Reduction to the actual primitive character, without multiplicities

At a fixed ambient modulus, passage to primitive characters is injective.
Thus grouping the sparse expansion introduces no coefficient multiplicity.
-/
namespace Ostmann
open scoped Classical

theorem primitiveCharacter_nontrivial {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro hh
  have he := χ.changeLevel_primitiveCharacter
  rw [hh, map_one] at he
  exact hχ he.symm

noncomputable def primitiveCharacterReduction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Option PrimitiveComplexCharacter :=
  if hχ : χ = 1 then none else some
    { modulus := χ.conductor
      positive := Nat.pos_of_ne_zero χ.conductor_ne_zero
      character := χ.primitiveCharacter
      primitive := χ.primitiveCharacter_isPrimitive
      nontrivial := primitiveCharacter_nontrivial χ hχ }

noncomputable def liftPrimitiveCharacter (N : ℕ)
    (e : Option PrimitiveComplexCharacter) : DirichletCharacter ℂ N :=
  match e with
  | none => 1
  | some χ => if h : χ.modulus ∣ N then DirichletCharacter.changeLevel h χ.character else 1

theorem lift_primitiveCharacterReduction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    liftPrimitiveCharacter N (primitiveCharacterReduction χ) = χ := by
  unfold primitiveCharacterReduction
  split_ifs with hχ
  · simpa only [liftPrimitiveCharacter] using hχ.symm
  · simp only [liftPrimitiveCharacter, χ.conductor_dvd_level, dite_true]
    exact χ.changeLevel_primitiveCharacter

theorem primitiveCharacterReduction_injective (N : ℕ) [NeZero N] :
    Function.Injective (primitiveCharacterReduction (N := N)) := by
  intro χ ψ h
  have he := congrArg (liftPrimitiveCharacter N) h
  simpa only [lift_primitiveCharacterReduction] using he

theorem primitiveCharacterReduction_modulus {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (ρ : PrimitiveComplexCharacter)
    (hρ : primitiveCharacterReduction χ = some ρ) : ρ.modulus = χ.conductor := by
  unfold primitiveCharacterReduction at hρ
  split_ifs at hρ
  have he := Option.some.inj hρ
  exact (congrArg PrimitiveComplexCharacter.modulus he).symm

theorem primitiveCharacterReduction_modulus_le {N d : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hd : χ.FactorsThrough d)
    (ρ : PrimitiveComplexCharacter) (hρ : primitiveCharacterReduction χ = some ρ) :
    ρ.modulus ≤ d := by
  rw [primitiveCharacterReduction_modulus χ ρ hρ]
  apply Nat.le_of_dvd
  · have hd0 : d ≠ 0 := by
      intro h
      have hh := hd.dvd
      rw [h] at hh
      exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hh)
    exact Nat.pos_of_ne_zero hd0
  · exact χ.conductor_dvd_of_mem_conductorSet hd

end Ostmann

end OAI
