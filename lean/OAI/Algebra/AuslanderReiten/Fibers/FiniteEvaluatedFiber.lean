import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleEvaluation
import OAI.Algebra.AuslanderReiten.Fibers.FiniteFiberSides
import OAI.Algebra.AuslanderReiten.Stable.StableProjectiveSummand
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedProduct

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct
universe u
variable {k S : Type u} [Field k] [Ring S] [Algebra k S] [Module.Finite k S]

def pairModule (U V : FiniteLeftModule k S) : FiniteLeftModule k S where
  carrier := ModuleCat.of S (U.carrier × V.carrier)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance

variable (U V Y : FiniteLeftModule k S)

def fiberReassociate : (fiberSource U V Y).carrier ≃ₗ[S]
    ((pairModule U V).carrier × Y.canonicalFreeCover.carrier) where
  toFun z := ((z.1, z.2.1), z.2.2)
  invFun z := (z.1.1, z.1.2, z.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fiberPairProjection : (fiberSource U V Y).carrier →ₗ[S] (pairModule U V).carrier :=
  (LinearMap.fst S U.carrier (V.carrier × Y.canonicalFreeCover.carrier)).prod
    ((LinearMap.fst S V.carrier Y.canonicalFreeCover.carrier).comp
      (LinearMap.snd S U.carrier (V.carrier × Y.canonicalFreeCover.carrier)))

def fiberPairStableIso : StableIsomorphism S (fiberSource U V Y).carrier (pairModule U V).carrier := by
  letI := Y.canonicalFreeCover_projective
  letI := Y.canonicalFreeCover_finite
  exact (StableIsomorphism.ofLinearEquiv (fiberReassociate U V Y)).trans
    (StableIsomorphism.dropRight (R := S))

@[simp] theorem fiberPairStableIso_hom : (fiberPairStableIso U V Y).hom =
    StableHom.classOf S _ _ (fiberPairProjection U V Y) := by
  change StableHom.comp (StableHom.classOf S _ _ (LinearMap.fst S _ _))
    (StableHom.classOf S _ _ (fiberReassociate U V Y).toLinearMap) = _
  rw [StableHom.comp_classOf]
  rfl

section Evaluation
variable {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (U₁ U₂ Y₀ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

def evaluatedPairEquiv : (evaluated X (pairModule U₁ U₂)).carrier ≃ₗ[R]
    ((evaluated X U₁).carrier × (evaluated X U₂).carrier) :=
  EnvelopingBimodule.tensorProdEquiv U₁.carrier U₂.carrier X.carrier

def middlePairMap : (evaluated X (fiberSource U₁ U₂ Y₀)).carrier →ₗ[R]
    ((evaluated X U₁).carrier × (evaluated X U₂).carrier) :=
  (evaluatedPairEquiv X U₁ U₂).toLinearMap.comp
    (evaluationMap X (fiberPairProjection U₁ U₂ Y₀))

def evaluatedMiddleStableIso : StableIsomorphism R
    (evaluated X (fiberSource U₁ U₂ Y₀)).carrier
    ((evaluated X U₁).carrier × (evaluated X U₂).carrier) :=
  (evaluationStableIso X (fiberPairStableIso U₁ U₂ Y₀)).trans
    (StableIsomorphism.ofLinearEquiv (evaluatedPairEquiv X U₁ U₂))

@[simp] theorem evaluatedMiddleStableIso_hom : (evaluatedMiddleStableIso X U₁ U₂ Y₀).hom =
    StableHom.classOf R _ _ (middlePairMap X U₁ U₂ Y₀) := by
  change StableHom.comp (StableHom.classOf R _ _ (evaluatedPairEquiv X U₁ U₂).toLinearMap)
    (EnvelopingBimodule.stableEvaluation X.carrier (fiberPairStableIso U₁ U₂ Y₀).hom) = _
  rw [fiberPairStableIso_hom, EnvelopingBimodule.stableEvaluation_classOf]
  erw [StableHom.comp_classOf]

variable (g₁ : U₁.carrier ⟶ Y₀.carrier) (g₂ : U₂.carrier ⟶ Y₀.carrier)

theorem middlePairMap_fiberInclusion :
    (middlePairMap X U₁ U₂ Y₀).comp
      (evaluationMap X (fiberInclusion U₁ U₂ Y₀ g₁ g₂).hom) =
    (evaluationMap X (fiberProjection₁ U₁ U₂ Y₀ g₁ g₂).hom).prod
      (evaluationMap X (fiberProjection₂ U₁ U₂ Y₀ g₁ g₂).hom) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R)
  intro m x
  rfl

theorem fiberFunctionExact : Function.Exact
    (fiberInclusion U₁ U₂ Y₀ g₁ g₂).hom (fiberMap U₁ U₂ Y₀ g₁ g₂).hom := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property

variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R Y₀.carrier)]

def evaluatedFiberTriangle (τ : FrobeniusTrace k R) :
    Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  evaluationTriangle X (fiberInclusion U₁ U₂ Y₀ g₁ g₂).hom (fiberMap U₁ U₂ Y₀ g₁ g₂).hom
    Subtype.val_injective (fiberMap_surjective U₁ U₂ Y₀ g₁ g₂)
    (fiberFunctionExact U₁ U₂ Y₀ g₁ g₂) τ

 theorem evaluatedFiberTriangle_distinguished (τ : FrobeniusTrace k R) :
    evaluatedFiberTriangle X U₁ U₂ Y₀ g₁ g₂ τ ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  evaluationTriangle_distinguished _ _ _ _ _ _ _

end Evaluation
end ArExplicit.FiniteLeftModule

end

end OAI
