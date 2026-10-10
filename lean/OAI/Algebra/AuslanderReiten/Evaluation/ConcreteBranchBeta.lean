import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBetaTransfer
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBetaHom
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBranchTop

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

private theorem compositeValue {C : Type*} [Category C]
    {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {a : W ⟶ Y} {b : W ⟶ Z} (ha : f ≫ g = a) (hb : a ≫ h = b) :
    f ≫ g ≫ h = b := by
  rw [← Category.assoc, ha, hb]

universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)

def branchBetaDetector : (evaluatedSimpleObject q ⟶ branchTargetObject q) →ₗ[k]
    (evaluatedSimpleObject q ⟶ (HomotopyCategory.quotient _ _).obj
      ((A.betaFiniteModule q).completeCochain (AFrobeniusTrace k q))) where
  toFun u := u ≫ evaluatedFiniteTargetTop q ≫
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
        (M := evaluatedBaseModule q 1) (N := A.betaFiniteModule q) (betaTransfer q hq))
  map_add' u v := by simp only [Preadditive.add_comp]
  map_smul' a u := by simp only [Linear.smul_comp, RingHom.id_apply]

theorem branchBetaDetector_value (H : kˣ) :
    branchBetaDetector q hq (branchHom q H) =
      (HomotopyCategory.quotient _ _).map
        (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
          (M := A.simpleFiniteModule q) (N := A.betaFiniteModule q)
          ((betaTransfer q hq).comp (normalizedBranchTop q H))) := by
  change branchHom q H ≫ (evaluatedFiniteTargetTop q ≫ _) = _
  exact compositeValue (branchHom_top q H)
    (FiniteLeftModule.resolutionMap_comp (AFrobeniusTrace k q)
      (M := A.simpleFiniteModule q) (N := evaluatedBaseModule q 1) (L := A.betaFiniteModule q)
      (normalizedBranchTop q H) (betaTransfer q hq)).symm

end ArExplicit.T

end

end OAI
