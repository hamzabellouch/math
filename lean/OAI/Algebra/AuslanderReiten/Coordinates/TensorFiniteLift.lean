import OAI.Algebra.AuslanderReiten.Cones.BimoduleTwoConeSides
import OAI.Algebra.AuslanderReiten.Tensor.TwistedTensorResolution
import OAI.Algebra.AuslanderReiten.Cones.TwoConeShiftedMap
import OAI.Algebra.AuslanderReiten.Fibers.BimoduleFiber

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Ae" => ExternalTensor.EnvelopingProduct k R R

theorem bimodule_term_finite_k (n : ℕ) :
    Module.Finite k ((bimoduleTwoConeData q).term n) := by
  let := bimodule_term_finite q n
  exact Module.Finite.trans Ae _

theorem source_term_finite_k (n : ℕ) :
    Module.Finite k ((sourceData q H).term n) := by
  let := source_finite q H n
  exact Module.Finite.trans Ae _

abbrev firstTailModule : FiniteLeftModule k Ae :=
  TwoCone.cokernelModule (bimoduleTwoConeData q) (bimodule_term_finite_k q) 1

def sourceAugmentationEquiv :
    (twistedFiniteModule (sourceTwist q H)).carrier ≃ₗ[Ae]
      (TwoCone.baseCokernelModule (sourceData q H) (source_term_finite_k q H) 0).carrier :=
  (sourceBaseEquiv q H).symm

def sourceFourthToTail :
    (TwoCone.baseCokernelModule (sourceData q H) (source_term_finite_k q H) 4).carrier →ₗ[Ae]
      (firstTailModule q).carrier :=
  (tailMap q H).comp (sourceFourthEquiv q H).symm.toLinearMap

def sourceShiftIso :=
  TwoCone.tailSourceShiftIso (sourceData q H) (source_term_finite_k q H)
    (AEnvelopingFrobeniusTrace k q) (source_exact q H) (source_projective q H)
    (U := twistedFiniteModule (sourceTwist q H)) 4 (sourceAugmentationEquiv q H)

def finiteLift : (twistedFiniteModule (sourceTwist q H)).carrier →ₗ[Ae]
    ((firstTailModule q).canonicalCosyzygies 4).carrier :=
  FiniteLeftModule.shiftedModuleMap (AEnvelopingFrobeniusTrace k q)
    (U := twistedFiniteModule (sourceTwist q H))
    (M := TwoCone.baseCokernelModule (sourceData q H) (source_term_finite_k q H) 4)
    (N := firstTailModule q) 4 (sourceShiftIso q H) (sourceFourthToTail q H)

def finiteLiftClass :=
  FiniteLeftModule.shiftedResolutionMap (AEnvelopingFrobeniusTrace k q)
    (U := twistedFiniteModule (sourceTwist q H))
    (M := TwoCone.baseCokernelModule (sourceData q H) (source_term_finite_k q H) 4)
    (N := firstTailModule q) 4 (sourceShiftIso q H) (sourceFourthToTail q H)

theorem finiteLift_spec :
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap (AEnvelopingFrobeniusTrace k q) (finiteLift q H)) =
        finiteLiftClass q H :=
  FiniteLeftModule.shiftedModuleMap_spec (AEnvelopingFrobeniusTrace k q) 4
    (sourceShiftIso q H) (sourceFourthToTail q H)

theorem firstTailModule_left_projective :
    Module.Projective (A k q)
      ((ModuleCat.restrictScalars (tensorLeftInclusion k (A k q) (A k q)ᵐᵒᵖ)).obj
        (firstTailModule q).carrier) := firstTail_left_projective q

theorem firstTailModule_right_projective :
    Module.Projective (A k q)ᵐᵒᵖ
      ((ModuleCat.restrictScalars (tensorRightInclusion k (A k q) (A k q)ᵐᵒᵖ)).obj
        (firstTailModule q).carrier) := firstTail_right_projective q

theorem firstTailModule_left_finite :
    Module.Finite (A k q)
      ((ModuleCat.restrictScalars (tensorLeftInclusion k (A k q) (A k q)ᵐᵒᵖ)).obj
        (firstTailModule q).carrier) := firstTail_left_finite q

theorem firstTailModule_right_finite :
    Module.Finite (A k q)ᵐᵒᵖ
      ((ModuleCat.restrictScalars (tensorRightInclusion k (A k q) (A k q)ᵐᵒᵖ)).obj
        (firstTailModule q).carrier) := firstTail_right_finite q

end ArExplicit.T

end

end OAI
