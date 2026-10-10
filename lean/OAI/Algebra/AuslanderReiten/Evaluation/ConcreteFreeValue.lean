import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteFreePure
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteFreeExtension

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local instance (priority := 3000) valueNativeScalar : Module k (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).scalar
local instance (priority := 3000) valueNativeTower : IsScalarTower k (A k q) (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).tower

theorem freeCoordinateRaw_endpoint (z : (D).term 0) (s t : Resolution.Simple q) :
    freeCoordinateRaw q hq (BalancedTensor.tmul
      (⟨z⟩ : EnvelopingBimodule k (A k q) (TwoCone.termModule D hf 0).carrier) (s ⊗ₜ[k] t)) =
      endpointEvaluation q s t z :=
  freeCoordinateRaw_eq_endpointEvaluation q hq (freeCoordinateRaw_endpoint_pure q hq) z s t

end ArExplicit.T

end

end OAI
