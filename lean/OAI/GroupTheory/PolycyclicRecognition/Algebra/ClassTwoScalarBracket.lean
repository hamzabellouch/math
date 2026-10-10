import OAI.GroupTheory.PolycyclicRecognition.Algebra.ClassTwoExteriorBracket
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarExteriorSurjection
import Mathlib.LinearAlgebra.ExteriorPower.Basis

namespace OAI

/-! # Field-valued brackets of the actual central derived layer -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct IsMulCommutative
variable {G : Type} [Group G] (K : Type) [Field K]

def centralDerivedAlternating (h : commutator G ≤ Subgroup.center G) :
    Additive (Abelianization G) [⋀^Fin 2]→ₗ[ℤ] centralDerivedSubmodule (G := G) :=
  (centerCommutatorAlternating h).codRestrict _
    (fun v => centerCommutatorPairing_mem_derived h (v 0) (v 1))

theorem centralDerivedAlternating_exterior (h : commutator G ≤ Subgroup.center G) :
    exteriorPower.alternatingMapLinearEquiv (centralDerivedAlternating h) =
      centralDerivedExteriorBracket h := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.alternatingMapLinearEquiv (centralDerivedAlternating h)
      (exteriorPower.ιMulti ℤ 2 v) =
    centralDerivedExteriorBracket h (exteriorPower.ιMulti ℤ 2 v)
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  apply Subtype.ext
  change centerCommutatorAlternating h v =
    centerExteriorBracket h (exteriorPower.ιMulti ℤ 2 v)
  exact (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (centerCommutatorAlternating h) v).symm

def scalarCentralDerivedBracket (h : commutator G ≤ Subgroup.center G) :
    (⋀[K]^2 (K ⊗[ℤ] Additive (Abelianization G))) →ₗ[K]
      K ⊗[ℤ] centralDerivedSubmodule (G := G) :=
  scalarExteriorPresentation K (centralDerivedAlternating h)

theorem scalarCentralDerivedBracket_surjective
    (h : commutator G ≤ Subgroup.center G) :
    Function.Surjective (scalarCentralDerivedBracket K h) := by
  apply scalarExteriorPresentation_surjective
  rw [centralDerivedAlternating_exterior]
  exact centralDerivedExteriorBracket_surjective h

theorem scalarCentralDerived_finite
    (h : commutator G ≤ Subgroup.center G)
    [Module.Finite K (K ⊗[ℤ] Additive (Abelianization G))] :
    Module.Finite K (K ⊗[ℤ] centralDerivedSubmodule (G := G)) :=
  Module.Finite.of_surjective (scalarCentralDerivedBracket K h)
    (scalarCentralDerivedBracket_surjective K h)

def centralDerivedAddEquiv [IsMulCommutative (commutator G)]
    (h : commutator G ≤ Subgroup.center G) :
    centralDerivedSubmodule (G := G) ≃+ Additive (commutator G) where
  toFun z := Additive.ofMul ⟨z.val.toMul.val, z.property⟩
  invFun z := ⟨Additive.ofMul ⟨z.toMul.val, h z.toMul.property⟩, z.toMul.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem classTwo_scalar_derived_finite [IsMulCommutative (commutator G)]
    (h : commutator G ≤ Subgroup.center G)
    [Module.Finite K (K ⊗[ℤ] Additive (Abelianization G))] :
    Module.Finite K (K ⊗[ℤ] Additive (commutator G)) := by
  let := scalarCentralDerived_finite K h
  let e := LinearEquiv.baseChange ℤ K _ _ (centralDerivedAddEquiv h).toIntLinearEquiv
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end PolycyclicRecognition

end

end OAI
