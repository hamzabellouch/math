import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleBarProductPrism
import Mathlib.LinearAlgebra.ExteriorPower.Basic

namespace OAI

/-! # The integral exterior product in abelian group homology -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (A : Type) [CommGroup A]

def tupleBarAdditiveClass {n : ℕ} (v : Fin (n + 1) → Additive A) :
    groupHomology (integralTrivialCoefficient A) (n + 1) :=
  tupleBarProductClass (fun i => (v i).toMul)

theorem tupleBarAdditiveClass_update_add {n : ℕ} [hDec : DecidableEq (Fin (n + 1))]
    (v : Fin (n + 1) → Additive A)
    (i : Fin (n + 1)) (a b : Additive A) :
    tupleBarAdditiveClass A (Function.update v i (a + b)) =
      tupleBarAdditiveClass A (Function.update v i a) +
        tupleBarAdditiveClass A (Function.update v i b) := by
  cases Subsingleton.elim hDec (instDecidableEqFin (n + 1))
  change tupleBarProductClass (Additive.toMul ∘ Function.update v i (a + b)) =
    tupleBarProductClass (Additive.toMul ∘ Function.update v i a) +
      tupleBarProductClass (Additive.toMul ∘ Function.update v i b)
  rw [Function.comp_update, Function.comp_update, Function.comp_update]
  exact tupleBarProductClass_update_mul (fun j => (v j).toMul) i a.toMul b.toMul

def tupleBarClassCoordinate {n : ℕ} [DecidableEq (Fin (n + 1))]
    (v : Fin (n + 1) → Additive A) (i : Fin (n + 1)) :
    Additive A →+ groupHomology (integralTrivialCoefficient A) (n + 1) :=
  AddMonoidHom.mk' (fun a => tupleBarAdditiveClass A (Function.update v i a))
    (tupleBarAdditiveClass_update_add A v i)

def tupleBarAlternating (n : ℕ) :
    Additive A [⋀^Fin (n + 1)]→ₗ[ℤ] groupHomology (integralTrivialCoefficient A) (n + 1) where
  toFun := tupleBarAdditiveClass A
  map_update_add' := by
    intro _ v i a b
    exact tupleBarAdditiveClass_update_add A v i a b
  map_update_smul' := by
    intro _ v i r a
    exact map_intCast_smul (tupleBarClassCoordinate A v i) ℤ ℤ r a
  map_eq_zero_of_eq' := by
    intro v i j h hij
    exact tupleBarProductClass_eq_zero_of_eq _ (congrArg Additive.toMul h) hij

def tupleBarExteriorProduct (n : ℕ) :
    (⋀[ℤ]^(n + 1) (Additive A)) →ₗ[ℤ]
      groupHomology (integralTrivialCoefficient A) (n + 1) :=
  exteriorPower.alternatingMapLinearEquiv (tupleBarAlternating A n)

@[simp] theorem tupleBarExteriorProduct_value (n : ℕ) (v : Fin (n + 1) → Additive A) :
    tupleBarExteriorProduct A n (exteriorPower.ιMulti ℤ (n + 1) v) =
      tupleBarAdditiveClass A v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

end PolycyclicRecognition

end

end OAI
