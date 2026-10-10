import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterComplexification
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedLogDerivative
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroReflection

namespace OAI

/-! # The actual functional equation for a real primitive character -/

namespace Ostmann

open Complex
open scoped Classical

theorem PrimitiveRealCharacter.complex_inv_eq (χ : PrimitiveRealCharacter) :
    χ.complexCharacter⁻¹ = χ.complexCharacter := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  rw [← MulChar.star_eq_inv]
  ext x
  simp [PrimitiveRealCharacter.complexCharacter]

theorem PrimitiveRealCharacter.inverse_completed_eq (χ : PrimitiveRealCharacter) :
    χ.asComplex.inverse.completed = χ.asComplex.completed := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  funext s
  change DirichletCharacter.completedLFunction (χ.complexCharacter⁻¹) s =
    DirichletCharacter.completedLFunction χ.complexCharacter s
  rw [χ.complex_inv_eq]

theorem PrimitiveRealCharacter.inverse_L_eq (χ : PrimitiveRealCharacter) :
    χ.asComplex.inverse.L = χ.asComplex.L := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  funext s
  change DirichletCharacter.LFunction (χ.complexCharacter⁻¹) s =
    DirichletCharacter.LFunction χ.complexCharacter s
  rw [χ.complex_inv_eq]

theorem PrimitiveRealCharacter.completed_logDeriv_reflection
    (χ : PrimitiveRealCharacter) (s : ℂ) (hs : 1 ≤ s.re) :
    logDeriv χ.asComplex.completed (1 - s) =
      -Complex.log (χ.modulus : ℂ) - logDeriv χ.asComplex.completed s := by
  have hh := χ.asComplex.completed_logDeriv_reflection s hs
  rw [χ.inverse_completed_eq] at hh
  exact hh

theorem PrimitiveRealCharacter.zero_reflection_order (χ : PrimitiveRealCharacter)
    (z : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1) :
    analyticOrderNatAt χ.L (1 - z) = analyticOrderNatAt χ.L z := by
  have hh := χ.asComplex.L_order_reflection z hz hz1
  rw [χ.inverse_L_eq] at hh
  exact congrArg ENat.toNat hh

end Ostmann

end OAI
