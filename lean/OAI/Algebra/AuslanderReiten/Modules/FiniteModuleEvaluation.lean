import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedExact
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingStableEvaluation
import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionLinear
import OAI.Algebra.AuslanderReiten.Complete.ProjectiveCompleteResolution

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct

namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (M : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

def evaluated : FiniteLeftModule k R where
  carrier := ModuleCat.of R (BalancedTensor k R (EnvelopingBimodule k R M.carrier) X.carrier)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance

variable {M N P : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}

def evaluationMap (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier) :
    (evaluated X M).carrier →ₗ[R] (evaluated X N).carrier :=
  EnvelopingBimodule.tensorMap X.carrier (ModuleCat.ofHom f)

omit [Module.Finite k R] in
@[simp] theorem evaluationMap_id : evaluationMap X (LinearMap.id : M.carrier →ₗ[_] M.carrier) =
    LinearMap.id := EnvelopingBimodule.tensorMap_id X.carrier

omit [Module.Finite k R] in
@[simp] theorem evaluationMap_comp (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier)
    (g : N.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P.carrier) :
    evaluationMap X (g.comp f) = (evaluationMap X g).comp (evaluationMap X f) :=
  EnvelopingBimodule.tensorMap_comp X.carrier (ModuleCat.ofHom f) (ModuleCat.ofHom g)

def evaluationStableIso (e : StableIsomorphism (R ⊗[k] Rᵐᵒᵖ) M.carrier N.carrier) :
    StableIsomorphism R (evaluated X M).carrier (evaluated X N).carrier where
  hom := EnvelopingBimodule.stableEvaluation X.carrier e.hom
  inv := EnvelopingBimodule.stableEvaluation X.carrier e.inv
  hom_inv_id := by
    erw [← EnvelopingBimodule.stableEvaluation_comp, e.hom_inv_id]
    exact EnvelopingBimodule.stableEvaluation_id X.carrier
  inv_hom_id := by
    erw [← EnvelopingBimodule.stableEvaluation_comp, e.inv_hom_id]
    exact EnvelopingBimodule.stableEvaluation_id X.carrier

omit [Module.Finite k R] in
theorem evaluated_projective [Module.Projective (R ⊗[k] Rᵐᵒᵖ) M.carrier] :
    Module.Projective R (evaluated X M).carrier := by
  let := Module.Finite.of_restrictScalars_finite k (R ⊗[k] Rᵐᵒᵖ) M.carrier
  exact EnvelopingBimodule.tensor_projective X.carrier M.carrier

variable (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier)
  (g : N.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R P.carrier)]

include hf hg he in
omit [Module.Finite k R] in

theorem evaluation_shortExact :
    Function.Injective (evaluationMap X f) ∧ Function.Surjective (evaluationMap X g) ∧
      Function.Exact (evaluationMap X f) (evaluationMap X g) := by
  have hr : LinearMap.range f = LinearMap.ker g := by
    ext y
    exact (he y).symm
  obtain ⟨hi, hs, hx⟩ := EnvelopingBimodule.tensorMap_shortExact X.carrier
    (ModuleCat.ofHom f) (ModuleCat.ofHom g) hf hg hr
  change LinearMap.range (evaluationMap X f) = LinearMap.ker (evaluationMap X g) at hx
  refine ⟨hi, hs, ?_⟩
  intro y
  exact (show y ∈ LinearMap.ker (evaluationMap X g) ↔
      y ∈ LinearMap.range (evaluationMap X f) by rw [hx])

variable (τ : FrobeniusTrace k R)

def evaluationTriangle : Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  resolutionTriangle τ (evaluationMap X f) (evaluationMap X g)
    (evaluation_shortExact X f g hf hg he).1 (evaluation_shortExact X f g hf hg he).2.1
    (evaluation_shortExact X f g hf hg he).2.2

theorem evaluationTriangle_distinguished : evaluationTriangle X f g hf hg he τ ∈
    distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  resolutionTriangle_distinguished _ _ _ _ _ _

def evaluationSuccessorIso [Module.Projective (R ⊗[k] Rᵐᵒᵖ) N.carrier] :
    (HomotopyCategory.quotient _ _).obj ((evaluated X P).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((evaluated X M).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI := evaluated_projective X (M := N)
  exact projectiveMiddleShiftIso τ (evaluationMap X f) (evaluationMap X g)
    (evaluation_shortExact X f g hf hg he).1 (evaluation_shortExact X f g hf hg he).2.1
    (evaluation_shortExact X f g hf hg he).2.2

@[simp]
theorem evaluationSuccessorIso_hom [Module.Projective (R ⊗[k] Rᵐᵒᵖ) N.carrier] :
    (evaluationSuccessorIso X f g hf hg he τ).hom =
      (evaluationTriangle X f g hf hg he τ).mor₃ := by
  let := evaluated_projective X (M := N)
  exact projectiveMiddleShiftIso_hom _ _ _ _ _ _

section Naturality
variable {M₁ N₁ P₁ M₂ N₂ P₂ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}
variable (f₁ : M₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N₁.carrier)
  (g₁ : N₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P₁.carrier)
  (f₂ : M₂.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N₂.carrier)
  (g₂ : N₂.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P₂.carrier)
variable (hf₁ : Function.Injective f₁) (hg₁ : Function.Surjective g₁) (he₁ : Function.Exact f₁ g₁)
  (hf₂ : Function.Injective f₂) (hg₂ : Function.Surjective g₂) (he₂ : Function.Exact f₂ g₂)
variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R P₁.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R P₂.carrier)]
variable (a : M₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] M₂.carrier)
  (b : N₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N₂.carrier)
  (c : P₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P₂.carrier)

theorem evaluationConnecting_natural
    (hab : b.comp f₁ = f₂.comp a) (hbc : g₂.comp b = c.comp g₁) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X c)) ≫
      (evaluationTriangle X f₂ g₂ hf₂ hg₂ he₂ τ).mor₃ =
    (evaluationTriangle X f₁ g₁ hf₁ hg₁ he₁ τ).mor₃ ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
        ((HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X a))) := by
  apply resolutionConnecting_natural
  · rw [← evaluationMap_comp, ← evaluationMap_comp, hab]
  · rw [← evaluationMap_comp, ← evaluationMap_comp, hbc]
end Naturality

end ArExplicit.FiniteLeftModule

end

end OAI
