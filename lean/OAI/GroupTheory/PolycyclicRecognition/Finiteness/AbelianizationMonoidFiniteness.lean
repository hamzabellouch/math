import OAI.GroupTheory.PolycyclicRecognition.Algebra.MonoidModuleAscendingBase
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianByFiniteContractor

namespace OAI

/-! # The one-sided module condition in the nilpotent finiteness argument

The monoid generator acts by the inverse of conjugation. Finite generation
over its integral monoid ring supplies an ascending base and hence virtual
solvability and a finite cohomological dimension bound.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra IsMulCommutative
variable {A : Type} [CommGroup A]

def mulAutIntegralLinear (α : MulAut A) : Additive A ≃ₗ[ℤ] Additive A :=
  α.toAdditive.toIntLinearEquiv

def inverseAutMonoidRepresentation (α : MulAut A) :
    Representation ℤ (Multiplicative ℕ) (Additive A) :=
  inverseIterateRepresentation (mulAutIntegralLinear α)

def additiveMultiplicativeEquiv : A ≃* Multiplicative (Additive A) where
  toFun x := Multiplicative.ofAdd (Additive.ofMul x)
  invFun x := x.toAdd.toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ascendingBase_of_monoidModule_finite (α : MulAut A)
    [hfinite : Module.Finite ℤ[Multiplicative ℕ] (inverseAutMonoidRepresentation α).asModule] :
    HasFinitelyGeneratedAscendingBase α := by
  let : Module.Finite ℤ[Multiplicative ℕ]
      (inverseIterateRepresentation (mulAutIntegralLinear α)).asModule := hfinite
  have h := monoidModule_ascendingBase (mulAutIntegralLinear α)
  exact h.of_equiv additiveMultiplicativeEquiv α
    (integralLinearMulAut (mulAutIntegralLinear α)) (fun _ => rfl)

variable {G : Type} [Group G] [Group.FG G]

theorem virtualSolvableFiniteDimension_of_abelianization_monoidFinite
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (H : Subgroup (G ⧸ N)) [H.Normal] [H.FiniteIndex] [IsMulCommutative H]
    (t : G)
    [Module.Finite ℤ[Multiplicative ℕ]
      (inverseAutMonoidRepresentation
        (characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) t))).asModule] :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  apply virtualSolvableFiniteDimension_of_abelianByFinite_contractor N H t
  exact ascendingBase_of_monoidModule_finite _

end PolycyclicRecognition

end

end OAI
