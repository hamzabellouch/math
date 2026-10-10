import OAI.Algebra.AuslanderReiten.Fibers.FiniteFiberComponents
import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberEvaluation
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedTriangleArrows

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "Y₀" => fiberTarget q
local notation "τ₀" => AFrobeniusTrace k q

def evaluatedBranchMap (H : kˣ) : (X₀).carrier →ₗ[R₀]
    (FiniteLeftModule.evaluated X₀ Y₀).carrier :=
  (FiniteLeftModule.evaluationMap X₀ (M := twistedFiniteModule (sourceTwist q H))
    (N := Y₀) (normalizedLift q H).hom).comp (evaluatedTwistEquiv q H).symm.toLinearMap

variable (H₁ H₂ : kˣ)
local notation "U₁" => twistedFiniteModule (sourceTwist q H₁)
local notation "U₂" => twistedFiniteModule (sourceTwist q H₂)

def evaluatedMiddleInl : (X₀).carrier →ₗ[R₀] (evaluatedMiddle q H₁ H₂).carrier :=
  (FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberSourceInl U₁ U₂ Y₀)).comp
    (evaluatedTwistEquiv q H₁).symm.toLinearMap

def evaluatedMiddleInr : (X₀).carrier →ₗ[R₀] (evaluatedMiddle q H₁ H₂).carrier :=
  (FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberSourceInr U₁ U₂ Y₀)).comp
    (evaluatedTwistEquiv q H₂).symm.toLinearMap

def evaluatedFiberSecond : (evaluatedMiddle q H₁ H₂).carrier →ₗ[R₀]
    (FiniteLeftModule.evaluated X₀ Y₀).carrier :=
  FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberMap U₁ U₂ Y₀
    (normalizedLift q H₁) (normalizedLift q H₂)).hom

theorem middleToSimplePair_inl : (middleToSimplePair q H₁ H₂).comp
    (evaluatedMiddleInl q H₁ H₂) = LinearMap.inl R₀ (X₀).carrier (X₀).carrier := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (FiniteLeftModule.middlePairMap_inl X₀ U₁ U₂ Y₀)
    ((evaluatedTwistEquiv q H₁).symm x)
  simp only [LinearMap.comp_apply] at h
  change (evaluatedTwistPairEquiv q H₁ H₂)
    ((FiniteLeftModule.middlePairMap X₀ U₁ U₂ Y₀)
      (FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberSourceInl U₁ U₂ Y₀)
        ((evaluatedTwistEquiv q H₁).symm x))) = _
  rw [h]
  change ((evaluatedTwistEquiv q H₁) ((evaluatedTwistEquiv q H₁).symm x),
    (evaluatedTwistEquiv q H₂) 0) = (x,0)
  simp

theorem middleToSimplePair_inr : (middleToSimplePair q H₁ H₂).comp
    (evaluatedMiddleInr q H₁ H₂) = LinearMap.inr R₀ (X₀).carrier (X₀).carrier := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (FiniteLeftModule.middlePairMap_inr X₀ U₁ U₂ Y₀)
    ((evaluatedTwistEquiv q H₂).symm x)
  simp only [LinearMap.comp_apply] at h
  change (evaluatedTwistPairEquiv q H₁ H₂)
    ((FiniteLeftModule.middlePairMap X₀ U₁ U₂ Y₀)
      (FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberSourceInr U₁ U₂ Y₀)
        ((evaluatedTwistEquiv q H₂).symm x))) = _
  rw [h]
  change ((evaluatedTwistEquiv q H₁) 0,
    (evaluatedTwistEquiv q H₂) ((evaluatedTwistEquiv q H₂).symm x)) = (0,x)
  simp

theorem evaluatedFiberSecond_inl : (evaluatedFiberSecond q H₁ H₂).comp
    (evaluatedMiddleInl q H₁ H₂) = evaluatedBranchMap q H₁ := by
  dsimp only [evaluatedFiberSecond, evaluatedMiddleInl, evaluatedBranchMap]
  rw [← LinearMap.comp_assoc, FiniteLeftModule.evaluatedFiberMap_inl]

theorem evaluatedFiberSecond_inr : (evaluatedFiberSecond q H₁ H₂).comp
    (evaluatedMiddleInr q H₁ H₂) = evaluatedBranchMap q H₂ := by
  dsimp only [evaluatedFiberSecond, evaluatedMiddleInr, evaluatedBranchMap]
  rw [← LinearMap.comp_assoc, FiniteLeftModule.evaluatedFiberMap_inr]

theorem fiberEvaluationTriangle_second : (fiberEvaluationTriangle q H₁ H₂).mor₂ =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ₀ (evaluatedFiberSecond q H₁ H₂)) := by
  let := fiberTarget_right_projective q
  exact FiniteLeftModule.evaluationTriangle_second X₀
    (FiniteLeftModule.fiberInclusion U₁ U₂ Y₀ (normalizedLift q H₁) (normalizedLift q H₂)).hom
    (FiniteLeftModule.fiberMap U₁ U₂ Y₀ (normalizedLift q H₁) (normalizedLift q H₂)).hom
    Subtype.val_injective
    (FiniteLeftModule.fiberMap_surjective U₁ U₂ Y₀ (normalizedLift q H₁) (normalizedLift q H₂))
    (FiniteLeftModule.fiberFunctionExact U₁ U₂ Y₀ (normalizedLift q H₁) (normalizedLift q H₂)) τ₀

end ArExplicit.T

end

end OAI
