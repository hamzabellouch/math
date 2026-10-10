import OAI.Algebra.AuslanderReiten.Fibers.FiberEvaluationMap
import OAI.Algebra.AuslanderReiten.Evaluation.TensorTwistEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "U₁" => twistedFiniteModule (sourceTwist q H₁)
local notation "U₂" => twistedFiniteModule (sourceTwist q H₂)
local notation "Y" => fiberTarget q

abbrev evaluatedFiber := FiniteLeftModule.evaluated X (finiteFiber q H₁ H₂)

abbrev evaluatedMiddle := FiniteLeftModule.evaluated X (FiniteLeftModule.fiberSource U₁ U₂ Y)

def evaluatedTwistPairEquiv :
    ((FiniteLeftModule.evaluated X U₁).carrier × (FiniteLeftModule.evaluated X U₂).carrier) ≃ₗ[R]
      ((X).carrier × (X).carrier) :=
  LinearEquiv.prodCongr (evaluatedTwistEquiv q H₁) (evaluatedTwistEquiv q H₂)

def middleToSimplePair : (evaluatedMiddle q H₁ H₂).carrier →ₗ[R] ((X).carrier × (X).carrier) :=
  (evaluatedTwistPairEquiv q H₁ H₂).toLinearMap.comp
    (FiniteLeftModule.middlePairMap X U₁ U₂ Y)

def middleSimpleStableIso : StableIsomorphism R (evaluatedMiddle q H₁ H₂).carrier
    ((X).carrier × (X).carrier) :=
  (FiniteLeftModule.evaluatedMiddleStableIso X U₁ U₂ Y).trans
    (StableIsomorphism.ofLinearEquiv (evaluatedTwistPairEquiv q H₁ H₂))

@[simp] theorem middleSimpleStableIso_hom : (middleSimpleStableIso q H₁ H₂).hom =
    StableHom.classOf R _ _ (middleToSimplePair q H₁ H₂) := by
  change StableHom.comp (StableHom.classOf R _ _ (evaluatedTwistPairEquiv q H₁ H₂).toLinearMap)
    (FiniteLeftModule.evaluatedMiddleStableIso X U₁ U₂ Y).hom = _
  rw [FiniteLeftModule.evaluatedMiddleStableIso_hom, StableHom.comp_classOf]
  rfl

def evaluatedRho₁ : (evaluatedFiber q H₁ H₂).carrier →ₗ[R] (X).carrier :=
  (evaluatedTwistEquiv q H₁).toLinearMap.comp
    (FiniteLeftModule.evaluationMap X (rho₁ q H₁ H₂).hom)

def evaluatedRho₂ : (evaluatedFiber q H₁ H₂).carrier →ₗ[R] (X).carrier :=
  (evaluatedTwistEquiv q H₂).toLinearMap.comp
    (FiniteLeftModule.evaluationMap X (rho₂ q H₁ H₂).hom)

def evaluatedFiberInclusion : (evaluatedFiber q H₁ H₂).carrier →ₗ[R]
    (evaluatedMiddle q H₁ H₂).carrier :=
  FiniteLeftModule.fiberEvaluationInclusion X U₁ U₂ Y
    (normalizedLift q H₁) (normalizedLift q H₂)

theorem middleToSimplePair_fiberInclusion :
    (middleToSimplePair q H₁ H₂).comp (evaluatedFiberInclusion q H₁ H₂) =
    (evaluatedRho₁ q H₁ H₂).prod (evaluatedRho₂ q H₁ H₂) := by
  apply BalancedTensor.leftHom_ext (k := k)
  intro m x
  rfl

theorem fiberTarget_right_projective : Module.Projective Rᵐᵒᵖ
    (EnvelopingBimodule k R (fiberTarget q).carrier) := by
  let := firstTailModule_right_finite q
  let := firstTailModule_right_projective q
  let := (BimoduleFiber.target_right (firstTailModule q) (AEnvelopingFrobeniusTrace k q)).2
  infer_instance

def fiberEvaluationTriangle :
    Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  letI := fiberTarget_right_projective q
  exact FiniteLeftModule.evaluatedFiberTriangle X U₁ U₂ Y
    (normalizedLift q H₁) (normalizedLift q H₂) (AFrobeniusTrace k q)

 theorem fiberEvaluationTriangle_distinguished : fiberEvaluationTriangle q H₁ H₂ ∈
    distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let := fiberTarget_right_projective q
  exact FiniteLeftModule.evaluatedFiberTriangle_distinguished X U₁ U₂ Y
    (normalizedLift q H₁) (normalizedLift q H₂) (AFrobeniusTrace k q)

end ArExplicit.T

end

end OAI
