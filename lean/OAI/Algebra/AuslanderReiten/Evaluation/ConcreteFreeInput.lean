import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteFreeCoefficient
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteEndpointInsertion

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)
local notation "R" => T k q
local notation "S" => Resolution.Simple q
local instance (priority := 3000) inputNativeScalar : Module k (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).scalar
local instance (priority := 3000) inputNativeTower : IsScalarTower k (A k q) (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).tower

private theorem appliedEndpointInsertion (a b c d : R) (s t : S) :
    type_of% (congrArg (ExternalBalanced.totalFreeEvaluation k R R S S
      (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq))
        (endpointCoordinates_insert q a b c d s t)) :=
  congrArg (ExternalBalanced.totalFreeEvaluation k R R S S
      (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq))
    (endpointCoordinates_insert q a b c d s t)

theorem freeCoordinateRaw_pure_inclusion (a b c d : R) (s t : S) :
    type_of% ((freeCoordinateRaw_tmul_transfer q hq
      ((endpointCoordinates q).symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))) s t).trans
        (appliedEndpointInsertion q hq a b c d s t)) :=
  (freeCoordinateRaw_tmul_transfer q hq
    ((endpointCoordinates q).symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))) s t).trans
      (appliedEndpointInsertion q hq a b c d s t)

end ArExplicit.T

end

end OAI
