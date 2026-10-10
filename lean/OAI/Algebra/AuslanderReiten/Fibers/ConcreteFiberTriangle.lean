import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberHomotopy
import OAI.Algebra.AuslanderReiten.Homology.TriangleMiddleTransport

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "τ" => AFrobeniusTrace k q
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

@[simp] theorem fiberEvaluationTriangle_first : (fiberEvaluationTriangle q H₁ H₂).mor₁ =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := evaluatedMiddle q H₁ H₂) τ (evaluatedFiberInclusion q H₁ H₂)) := rfl

def fiberProductTriangle : Triangle HC :=
  triangleReplaceMiddle (fiberEvaluationTriangle q H₁ H₂) (middleProductResolutionIso q H₁ H₂)

def fiberProductTriangleIso : fiberEvaluationTriangle q H₁ H₂ ≅ fiberProductTriangle q H₁ H₂ :=
  triangleReplaceMiddleIso _ _

 theorem fiberProductTriangle_distinguished : fiberProductTriangle q H₁ H₂ ∈ distTriang HC :=
  triangleReplaceMiddle_distinguished _ _ (fiberEvaluationTriangle_distinguished q H₁ H₂)

theorem fiberProductTriangle_first_fst : (fiberProductTriangle q H₁ H₂).mor₁ ≫ biprod.fst =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := X) τ (evaluatedRho₁ q H₁ H₂)) := by
  change ((fiberEvaluationTriangle q H₁ H₂).mor₁ ≫
    (middleProductResolutionIso q H₁ H₂).hom) ≫ biprod.fst = _
  erw [fiberEvaluationTriangle_first, Category.assoc]
  exact fiberInclusion_product_fst q H₁ H₂

theorem fiberProductTriangle_first_snd : (fiberProductTriangle q H₁ H₂).mor₁ ≫ biprod.snd =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := X) τ (evaluatedRho₂ q H₁ H₂)) := by
  change ((fiberEvaluationTriangle q H₁ H₂).mor₁ ≫
    (middleProductResolutionIso q H₁ H₂).hom) ≫ biprod.snd = _
  erw [fiberEvaluationTriangle_first, Category.assoc]
  exact fiberInclusion_product_snd q H₁ H₂

end ArExplicit.T

end

end OAI
