import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedMiddleCoordinates
import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionAdditive

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u v
private theorem rowBoundary {C : Type u} [Category.{v} C] [Preadditive C]
    (F : C ⥤ C) [F.Additive] {U V W B : C}
    (a b : U ⟶ V) (t : V ⟶ F.obj W) (s : U ⟶ F.obj B)
    (p r : B ⟶ W) {Z : C} (c d : W ⟶ Z) (row : B ⟶ Z)
    (delta : U ⟶ F.obj Z) (hrow : row = p ≫ c + r ≫ d)
    (hdelta : delta = s ≫ F.map row)
    (ha : a ≫ t = s ≫ F.map p) (hb : b ≫ t = s ≫ F.map r) :
    delta = (a ≫ t) ≫ F.map c + (b ≫ t) ≫ F.map d := by
  rw [hdelta, hrow, F.map_add, F.map_comp, F.map_comp, Preadditive.comp_add, ha, hb]
  simp only [Category.assoc]

private theorem resolutionRow
    {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
    (tau : FrobeniusTrace k R) {M N P : FiniteLeftModule k R}
    (a b : M.carrier →ₗ[R] N.carrier) (f g : N.carrier →ₗ[R] P.carrier)
    (row : M.carrier →ₗ[R] P.carrier) (h : row = f.comp a + g.comp b) :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau row) =
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau a) ≫
        (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau f) +
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau b) ≫
        (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau g) := by
  rw [h, FiniteLeftModule.resolutionMap_add,
    FiniteLeftModule.resolutionMap_comp, FiniteLeftModule.resolutionMap_comp]

variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

theorem evaluatedSingletonFst_step (n : ℕ) :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q n)) ≫
      (evaluatedBaseStepIso q (n+2)).hom =
    (TwoCone.evaluatedMiddleSuccessorIso D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ n).hom ≫
        ((Q₀).map (FiniteLeftModule.resolutionMap τ₀
          (evaluatedSingletonFst q (n+1))))⟦(1 : ℤ)⟧' := by
  rw [evaluatedSingletonFst_eq, evaluatedSingletonFst_eq]
  exact TwoCone.evaluatedMiddleProjection_step D₀ hf₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ true n

theorem evaluatedSingletonSnd_step (n : ℕ) :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)) ≫
      (evaluatedBaseStepIso q (n+2)).hom =
    (TwoCone.evaluatedMiddleSuccessorIso D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ n).hom ≫
        ((Q₀).map (FiniteLeftModule.resolutionMap τ₀
          (evaluatedSingletonSnd q (n+1))))⟦(1 : ℤ)⟧' := by
  rw [evaluatedSingletonSnd_eq, evaluatedSingletonSnd_eq]
  exact TwoCone.evaluatedMiddleProjection_step D₀ hf₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ false n

theorem simpleSkeletonConnecting_components (n : ℕ) :
    (simpleSkeletonTriangle q n).mor₃ =
      ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q n)) ≫
        (evaluatedBaseStepIso q (n+2)).hom) ≫
          (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ n)⟦(1 : ℤ)⟧' +
      ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)) ≫
        (evaluatedBaseStepIso q (n+2)).hom) ≫
          (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ n)⟦(1 : ℤ)⟧' := by
  exact rowBoundary
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat R₀) (ComplexShape.up ℤ)) (1 : ℤ))
    _ _ _ _ _ _ _ _ _ _
    (resolutionRow τ₀ (M := evaluatedSingletonModule q (n+1))
      (N := evaluatedBaseModule q (n+3)) (P := evaluatedBaseModule q n)
      (evaluatedSingletonFst q (n+1)) (evaluatedSingletonSnd q (n+1))
      _ _ _ (evaluatedRow_coordinates q n))
    (TwoCone.evaluatedSkeletonConnecting_eq D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ n)
    (evaluatedSingletonFst_step q n) (evaluatedSingletonSnd_step q n)

end ArExplicit.T

end

end OAI
