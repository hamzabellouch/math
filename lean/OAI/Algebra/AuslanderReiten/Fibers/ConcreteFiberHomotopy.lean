import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberEvaluation
import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionProduct

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "τ" => AFrobeniusTrace k q
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

def middlePairResolutionIso :
    (Q).obj ((evaluatedMiddle q H₁ H₂).completeCochain τ) ≅
      (Q).obj ((FiniteLeftModule.pairModule X X).completeCochain τ) :=
  FiniteLeftModule.stableResolutionIso (M := evaluatedMiddle q H₁ H₂)
    (N := FiniteLeftModule.pairModule X X) τ (middleSimpleStableIso q H₁ H₂)

@[simp] theorem middlePairResolutionIso_hom : (middlePairResolutionIso q H₁ H₂).hom =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedMiddle q H₁ H₂)
      (N := FiniteLeftModule.pairModule X X) τ (middleToSimplePair q H₁ H₂)) :=
  FiniteLeftModule.stableResolutionIso_hom_of_class τ _ _ (middleSimpleStableIso_hom q H₁ H₂)

def middleProductResolutionIso :
    (Q).obj ((evaluatedMiddle q H₁ H₂).completeCochain τ) ≅
      ((Q).obj ((X).completeCochain τ) ⊞ (Q).obj ((X).completeCochain τ)) :=
  (middlePairResolutionIso q H₁ H₂).trans (FiniteLeftModule.resolutionPairIso τ X X)

 theorem fiberInclusion_pairResolution :
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := evaluatedMiddle q H₁ H₂) τ (evaluatedFiberInclusion q H₁ H₂)) ≫
      (middlePairResolutionIso q H₁ H₂).hom =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := FiniteLeftModule.pairModule X X) τ
      ((evaluatedRho₁ q H₁ H₂).prod (evaluatedRho₂ q H₁ H₂))) := by
  erw [middlePairResolutionIso_hom, ← FiniteLeftModule.resolutionMap_comp,
    middleToSimplePair_fiberInclusion]

theorem fiberInclusion_product_fst :
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := evaluatedMiddle q H₁ H₂) τ (evaluatedFiberInclusion q H₁ H₂)) ≫
      (middleProductResolutionIso q H₁ H₂).hom ≫ biprod.fst =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := X) τ (evaluatedRho₁ q H₁ H₂)) := by
  simp only [middleProductResolutionIso, Iso.trans_hom, Category.assoc,
    FiniteLeftModule.resolutionPairIso_hom_fst]
  rw [← Category.assoc]
  erw [fiberInclusion_pairResolution q H₁ H₂]
  exact (FiniteLeftModule.resolutionMap_comp (M := evaluatedFiber q H₁ H₂)
    (N := FiniteLeftModule.pairModule X X) (L := X) τ
    ((evaluatedRho₁ q H₁ H₂).prod (evaluatedRho₂ q H₁ H₂))
    (FiniteLeftModule.pairFst X X)).symm

theorem fiberInclusion_product_snd :
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := evaluatedMiddle q H₁ H₂) τ (evaluatedFiberInclusion q H₁ H₂)) ≫
      (middleProductResolutionIso q H₁ H₂).hom ≫ biprod.snd =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := X) τ (evaluatedRho₂ q H₁ H₂)) := by
  simp only [middleProductResolutionIso, Iso.trans_hom, Category.assoc,
    FiniteLeftModule.resolutionPairIso_hom_snd]
  rw [← Category.assoc]
  erw [fiberInclusion_pairResolution q H₁ H₂]
  exact (FiniteLeftModule.resolutionMap_comp (M := evaluatedFiber q H₁ H₂)
    (N := FiniteLeftModule.pairModule X X) (L := X) τ
    ((evaluatedRho₁ q H₁ H₂).prod (evaluatedRho₂ q H₁ H₂))
    (FiniteLeftModule.pairSnd X X)).symm

end ArExplicit.T

end

end OAI
