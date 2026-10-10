import OAI.Analysis.Pureness.States.RegularizedStateExtendedAW
import OAI.Analysis.Pureness.Tensor.CauchySpatialFaithful

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped TensorProduct NNReal ENNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A))
variable (hy : y ≠ 0) (f : StateSpace y) (hA : IsNuclear.{u,0} A)

lemma regularizedStateSpatialExtension_injective :
    Function.Injective (regularizedStateSpatialExtension hsimple y hy f hA) :=
  (regularizedStateCauchyPositive hsimple y hy f).cauchySpatialExtension_injective
    (matrixStateAWPositive hsimple y hy f freeGroupScalarUltrafilter)
    (regularizedStateCauchyTriangle hsimple y hy f)
    (matrixStateAWPositive_triangle hsimple y hy f freeGroupScalarUltrafilter)
    ((regularizedStateCauchyPositive hsimple y hy f).cauchySourceGNS
      (regularizedStateCauchyTriangle hsimple y hy f))
    (finOneOriginalGNS (A := A))
    ((regularizedStateCauchyPositive hsimple y hy f).cauchySourceGNS_injective
      (regularizedStateCauchyTriangle hsimple y hy f))
    (finOneOriginalSpatialAW hsimple y hy f hA)
    (matrixStateFinOneAW hsimple y hy f freeGroupScalarUltrafilter)
    (reducedFreeGroupAWEmbedding hsimple y hy f)
    (finOneOriginalSpatialAW_tensor hsimple y hy f hA)
    (regularizedStateNormalization y f)
    (matrixStateFinOneAW_positive hsimple y hy f freeGroupScalarUltrafilter)
    ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS
      (regularizedStateCauchyTriangle hsimple y hy f))
    ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS_injective
      (regularizedStateCauchyTriangle hsimple y hy f))
    (regularizedStateNormalization_pos hsimple y hy f)

lemma regularizedStateSpatialExtension_isometry :
    Isometry (regularizedStateSpatialExtension hsimple y hy f hA) :=
  NonUnitalStarAlgHom.isometry _
    (regularizedStateSpatialExtension_injective hsimple y hy f hA)

include hA in

lemma regularizedStateSpatialTensor_finite
    (x : (regularizedStateCauchyPositive hsimple y hy f).CauchyFreeGroupTensorTarget
      (regularizedStateCauchyTriangle hsimple y hy f)) (hx : star x*x = 1) : x*star x = 1 := by
  let Φ := regularizedStateSpatialExtension hsimple y hy f hA
  have hs : Φ (star x*x) = star (Φ x)*Φ x :=
    (map_mul Φ (star x) x).trans (congrArg (fun v => v*Φ x) (map_star Φ x))
  have ht := regularizedStateExtendedAW_finite hsimple y hy f (Φ x)
    (hs.symm.trans ((congrArg Φ hx).trans (map_one Φ)))
  apply regularizedStateSpatialExtension_injective hsimple y hy f hA
  exact (map_mul Φ x (star x)).trans
    ((congrArg (fun v => Φ x*v) (map_star Φ x)).trans (ht.trans (map_one Φ).symm))
end CuntzPureness

end

end OAI
