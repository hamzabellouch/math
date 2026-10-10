import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleEvaluation
import OAI.Algebra.AuslanderReiten.Duality.FiniteStableResolutionIso

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R) (τe : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ))
variable (τ : FrobeniusTrace k R)
variable {M N P : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}

def evaluationResolutionMap
    (f : (HomotopyCategory.quotient _ _).obj (M.completeCochain τe) ⟶
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τe)) :
    (HomotopyCategory.quotient _ _).obj ((X.evaluated M).completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj ((X.evaluated N).completeCochain τ) :=
  (resolutionHomotopyEquiv τ (X.evaluated M) (X.evaluated N)).symm
    (EnvelopingBimodule.stableEvaluation X.carrier (resolutionHomotopyEquiv τe M N f))

@[simp] theorem evaluationResolutionMap_lift (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier) :
    evaluationResolutionMap X τe τ
      ((HomotopyCategory.quotient _ _).map (resolutionMap τe f)) =
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X f)) := by
  apply (resolutionHomotopyEquiv τ (X.evaluated M) (X.evaluated N)).injective
  simp only [evaluationResolutionMap, resolutionHomotopyEquiv_map]
  erw [AddEquiv.apply_symm_apply]
  rfl

theorem evaluationResolutionMap_comp
    (f : (HomotopyCategory.quotient _ _).obj (M.completeCochain τe) ⟶
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τe))
    (g : (HomotopyCategory.quotient _ _).obj (N.completeCochain τe) ⟶
      (HomotopyCategory.quotient _ _).obj (P.completeCochain τe)) :
    evaluationResolutionMap X τe τ (f ≫ g) =
      evaluationResolutionMap X τe τ f ≫ evaluationResolutionMap X τe τ g := by
  obtain ⟨f, rfl⟩ := resolutionMap_surjective τe f
  obtain ⟨g, rfl⟩ := resolutionMap_surjective τe g
  rw [← resolutionMap_comp, evaluationResolutionMap_lift,
    evaluationResolutionMap_lift, evaluationResolutionMap_lift,
    ← resolutionMap_comp, evaluationMap_comp]

@[simp] theorem evaluationResolutionMap_id :
    evaluationResolutionMap X τe τ (𝟙 ((HomotopyCategory.quotient _ _).obj (M.completeCochain τe))) = 𝟙 _ := by
  rw [← resolutionMap_id (M := M) τe, evaluationResolutionMap_lift,
    evaluationMap_id, resolutionMap_id]

def evaluationResolutionIso
    (e : (HomotopyCategory.quotient _ _).obj (M.completeCochain τe) ≅
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τe)) :
    (HomotopyCategory.quotient _ _).obj ((X.evaluated M).completeCochain τ) ≅
      (HomotopyCategory.quotient _ _).obj ((X.evaluated N).completeCochain τ) where
  hom := evaluationResolutionMap X τe τ e.hom
  inv := evaluationResolutionMap X τe τ e.inv
  hom_inv_id := by rw [← evaluationResolutionMap_comp, e.hom_inv_id, evaluationResolutionMap_id]
  inv_hom_id := by rw [← evaluationResolutionMap_comp, e.inv_hom_id, evaluationResolutionMap_id]

theorem evaluationResolutionMap_triangle
    (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier)
    (g : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P.carrier)
    (t : (HomotopyCategory.quotient _ _).obj (N.completeCochain τe) ⟶
      (HomotopyCategory.quotient _ _).obj (P.completeCochain τe))
    (h : (HomotopyCategory.quotient _ _).map (resolutionMap τe f) ≫ t =
      (HomotopyCategory.quotient _ _).map (resolutionMap τe g)) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X f)) ≫
        evaluationResolutionMap X τe τ t =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X g)) := by
  have he := congrArg (evaluationResolutionMap X τe τ) h
  erw [evaluationResolutionMap_comp X τe τ (M := M) (N := N) (P := P)
      ((HomotopyCategory.quotient _ _).map (resolutionMap τe f)) t,
    evaluationResolutionMap_lift X τe τ (M := M) (N := N) f,
    evaluationResolutionMap_lift X τe τ (M := M) (N := P) g] at he
  exact he

end ArExplicit.FiniteLeftModule

end

end OAI
