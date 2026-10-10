import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarAlternatingExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleBarExteriorProduct

namespace OAI

/-! # The higher exterior cross product over every field -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K A : Type) [Field K] [CommGroup A]

def scalarHigherBarAlternating (n : ℕ) :
    (K ⊗[ℤ] Additive A) [⋀^Fin (n + 1)]→ₗ[K]
      K ⊗[ℤ] groupHomology (integralTrivialCoefficient A) (n + 1) :=
  scalarAlternatingExtension K
    ((scalarTensorUnit K _).compAlternatingMap (tupleBarAlternating A n))

def scalarHigherExteriorProduct (n : ℕ) :
    (⋀[K]^(n + 1) (K ⊗[ℤ] Additive A)) →ₗ[K]
      K ⊗[ℤ] groupHomology (integralTrivialCoefficient A) (n + 1) :=
  exteriorPower.alternatingMapLinearEquiv (scalarHigherBarAlternating K A n)

@[simp] theorem scalarHigherExteriorProduct_value (n : ℕ)
    (v : Fin (n + 1) → K ⊗[ℤ] Additive A) :
    scalarHigherExteriorProduct K A n (exteriorPower.ιMulti K (n + 1) v) =
      scalarHigherBarAlternating K A n v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

@[simp] theorem scalarHigherBarAlternating_unit (n : ℕ) (v : Fin (n + 1) → Additive A) :
    scalarHigherBarAlternating K A n (fun i => scalarTensorUnit K _ (v i)) =
      scalarTensorUnit K _ (tupleBarAdditiveClass A v) := by
  rw [scalarHigherBarAlternating, scalarAlternatingExtension_unit]
  rfl

end PolycyclicRecognition

end

end OAI
