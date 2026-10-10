import OAI.Algebra.AuslanderReiten.Coordinates.TensorFiniteTop
import OAI.Algebra.AuslanderReiten.Fibers.ExplicitBimoduleFiber
import OAI.Algebra.AuslanderReiten.Evaluation.TensorSourceUnit
import OAI.Algebra.AuslanderReiten.Tensor.ExternalEnvelopingScalar
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCoordinates
import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionLinear

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "Ae" => ExternalTensor.EnvelopingProduct k R R
local notation "D" => bimoduleTwoConeData q
local notation "τ" => AEnvelopingFrobeniusTrace k q
local notation "hD" => bimodule_term_finite_k q
local notation "P₀" => AbsoluteBar.complex k R

def sourceUnit : (twistedFiniteModule (sourceTwist q H)).carrier := ⟨1⟩

theorem sourceAugmentationEquiv_unit :
    sourceAugmentationEquiv q H (sourceUnit q H) = Submodule.Quotient.mk (show (sourceData q H).term 0 from tensorBarUnit q H) := by
  change (sourceBaseEquiv q H).symm (sourceUnit q H) = _
  apply (sourceBaseEquiv q H).injective
  erw [LinearEquiv.apply_symm_apply, sourceBaseEquiv_barUnit]
  rfl

theorem finiteSourceTop_unit :
    TwoCone.baseStepInclusion D (bimodule_exact q) 0 (finiteSourceTop q H (sourceUnit q H)) =
      bimoduleEndpoint q H (tensorBarUnit q H) := by
  change TwoCone.baseStepInclusion D (bimodule_exact q) 0
    (bimoduleTopCokernel q H 0 (sourceAugmentationEquiv q H (sourceUnit q H))) = _
  rw [sourceAugmentationEquiv_unit]
  have h := bimoduleTopCokernel_mk q H 0 (show (sourceData q H).term 0 from tensorBarUnit q H)
  erw [h]
  exact (TwoCone.baseStepInclusion_mk D (bimodule_exact q) 0
    (bimoduleTopComparison q H 0 (tensorBarUnit q H))).trans
    (LinearMap.congr_fun (bimoduleTopComparison_zero q H) (tensorBarUnit q H))

def normalizedSourceTop : (twistedFiniteModule (sourceTwist q H)).carrier →ₗ[Ae]
    (TwoCone.baseCokernelModule D hD 1).carrier :=
  ((H : k)^2)⁻¹ • finiteSourceTop q H

theorem normalizedLift_top :
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := twistedFiniteModule (sourceTwist q H))
        (N := (firstTailModule q).canonicalCosyzygies 4) (normalizedLift q H).hom) ≫ finiteTargetTop q =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := twistedFiniteModule (sourceTwist q H))
        (N := TwoCone.baseCokernelModule D hD 1) (normalizedSourceTop q H)) := by
  change (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := twistedFiniteModule (sourceTwist q H))
        (N := (firstTailModule q).canonicalCosyzygies 4) (((H : k)^2)⁻¹ • finiteLift q H)) ≫ finiteTargetTop q =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := twistedFiniteModule (sourceTwist q H))
        (N := TwoCone.baseCokernelModule D hD 1) (((H : k)^2)⁻¹ • finiteSourceTop q H))
  rw [FiniteLeftModule.resolutionMap_smul, Linear.smul_comp, finiteLift_top,
    FiniteLeftModule.resolutionMap_smul]

attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def endpointEvaluation (s t : Resolution.Simple q) : (D).term 0 →ₗ[k] A k q :=
  (A.barZeroCoordinate q).comp ((squareEvaluation q s t).comp
    ((barPairCoordinates q).toLinearMap.comp
      ((ExternalTensor.moduleScalarCoordinates k Te Te ((P₀).X 0) ((P₀).X 0)).toLinearMap.comp
      (((ExternalTensor.bottomProjection k Te Te P₀ P₀ 0).restrictScalars k).comp
        (ExternalTensor.envelopingScalarEquiv k R R ((productTwoConeData q).term 0)).toLinearMap))))

theorem endpointEvaluation_unit (hq1 : 1+q ≠ 0) (s t : Resolution.Simple q) :
    endpointEvaluation q s t (bimoduleEndpoint q H (tensorBarUnit q H)) =
      (H : k)^2 • A.socleMap q (s ⊗ₜ[k] t) := by
  change A.barZeroCoordinate q (squareEvaluation q s t
    (barPairCoordinates q (ExternalTensor.bottomProjection k Te Te P₀ P₀ 0
      (tensorEndpoint q H (tensorBarUnit q H))))) = _
  exact tensorEndpoint_evaluated q H hq1 s t

theorem normalizedSourceTop_evaluated (hq1 : 1+q ≠ 0) (s t : Resolution.Simple q) :
    endpointEvaluation q s t
      (TwoCone.baseStepInclusion D (bimodule_exact q) 0
        (normalizedSourceTop q H (sourceUnit q H))) = A.socleMap q (s ⊗ₜ[k] t) := by
  simp only [normalizedSourceTop, LinearMap.smul_apply, LinearMap.map_smul_of_tower, map_smul]
  rw [finiteSourceTop_unit, endpointEvaluation_unit q H hq1, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 H.ne_zero), one_smul]

end ArExplicit.T

end

end OAI
