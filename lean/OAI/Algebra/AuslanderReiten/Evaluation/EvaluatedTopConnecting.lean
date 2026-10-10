import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedTopCoordinates
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedTriangleArrows

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u v
private theorem postBoundary {C : Type u} [Category.{v} C] (F : C ⥤ C)
    {U V W Z : C} (delta : U ⟶ F.obj W) (s : U ⟶ F.obj V)
    (t : V ⟶ W) (p : W ⟶ Z) (c : V ⟶ Z)
    (hd : delta = s ≫ F.map t) (hc : t ≫ p = c) :
    delta ≫ F.map p = s ≫ F.map c := by
  rw [hd, Category.assoc, ← F.map_comp, hc]

private theorem resolutionComposite
    {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
    (tau : FrobeniusTrace k R) {M N P : FiniteLeftModule k R}
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] P.carrier)
    (h : M.carrier →ₗ[R] P.carrier) (he : g.comp f = h) :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau f) ≫
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau g) =
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau h) := by
  rw [← FiniteLeftModule.resolutionMap_comp, he]

variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

def evaluatedAdjacentMap (n : ℕ) :=
  FiniteLeftModule.evaluationMap X₀
    (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
    (N := TwoCone.middleCokernelModule D₀ hf₀ n) (-(TwoCone.columnCokernelMap D₀ n))

theorem simpleSkeletonTriangle_second (n : ℕ) :
    (simpleSkeletonTriangle q n).mor₂ =
      (Q₀).map (FiniteLeftModule.resolutionMap τ₀
        (FiniteLeftModule.evaluationMap X₀
          (M := TwoCone.skeletonCokernelModule D₀ hf₀ n)
          (N := TwoCone.middleCokernelModule D₀ hf₀ n)
          (TwoCone.singletonCokernelProjection D₀ n))) := by
  exact TwoCone.evaluatedSkeletonTriangle_second D₀ hf₀ (bimodule_exact q)
    (baseTail_right_projective q) X₀ τ₀ n

theorem simpleTopConnecting_adjacent (n : ℕ) :
    (simpleTopTriangle q n).mor₃ ≫ (simpleSkeletonTriangle q n).mor₂⟦(1 : ℤ)⟧' =
      (evaluatedBaseStepIso q (n+4)).hom ≫
        ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedAdjacentMap q n)))⟦(1 : ℤ)⟧' := by
  rw [simpleSkeletonTriangle_second]
  exact postBoundary
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat R₀) (ComplexShape.up ℤ)) (1 : ℤ))
    _ _ _ _ _
    (TwoCone.evaluatedTopConnecting_eq D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ n)
    (resolutionComposite τ₀
      (M := evaluatedBaseModule q (n+5))
      (N := (X₀).evaluated (TwoCone.skeletonCokernelModule D₀ hf₀ n))
      (P := evaluatedSingletonModule q n) _ _ _ (evaluatedTopAdjacent q n))

end ArExplicit.T

end

end OAI
