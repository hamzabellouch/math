import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberComponents
import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberTriangle
import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionProductInclusions
import OAI.Algebra.AuslanderReiten.Coordinates.BranchHomCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

def branchHom (H : kˣ) : evaluatedSimpleObject q ⟶ branchTargetObject q :=
  (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedBranchMap q H))

variable (H₁ H₂ : kˣ)

theorem evaluatedMiddleInl_product :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedMiddleInl q H₁ H₂)) ≫
      (middleProductResolutionIso q H₁ H₂).hom = biprod.inl := by
  simp only [middleProductResolutionIso, Iso.trans_hom, ← Category.assoc,
    middlePairResolutionIso_hom]
  erw [← FiniteLeftModule.resolutionMap_comp, middleToSimplePair_inl]
  exact FiniteLeftModule.resolutionPairInl τ₀ X₀ X₀

theorem evaluatedMiddleInr_product :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedMiddleInr q H₁ H₂)) ≫
      (middleProductResolutionIso q H₁ H₂).hom = biprod.inr := by
  simp only [middleProductResolutionIso, Iso.trans_hom, ← Category.assoc,
    middlePairResolutionIso_hom]
  erw [← FiniteLeftModule.resolutionMap_comp, middleToSimplePair_inr]
  exact FiniteLeftModule.resolutionPairInr τ₀ X₀ X₀

theorem fiberProductTriangle_inl_second :
    biprod.inl ≫ (fiberProductTriangle q H₁ H₂).mor₂ = branchHom q H₁ := by
  rw [← evaluatedMiddleInl_product q H₁ H₂]
  change (_ ≫ (middleProductResolutionIso q H₁ H₂).hom) ≫
    ((middleProductResolutionIso q H₁ H₂).inv ≫ (fiberEvaluationTriangle q H₁ H₂).mor₂) = _
  erw [Category.assoc, Iso.hom_inv_id_assoc, fiberEvaluationTriangle_second]
  erw [← FiniteLeftModule.resolutionMap_comp, evaluatedFiberSecond_inl]
  rfl

theorem fiberProductTriangle_inr_second :
    biprod.inr ≫ (fiberProductTriangle q H₁ H₂).mor₂ = branchHom q H₂ := by
  rw [← evaluatedMiddleInr_product q H₁ H₂]
  change (_ ≫ (middleProductResolutionIso q H₁ H₂).hom) ≫
    ((middleProductResolutionIso q H₁ H₂).inv ≫ (fiberEvaluationTriangle q H₁ H₂).mor₂) = _
  erw [Category.assoc, Iso.hom_inv_id_assoc, fiberEvaluationTriangle_second]
  erw [← FiniteLeftModule.resolutionMap_comp, evaluatedFiberSecond_inr]
  rfl

end ArExplicit.T

end

end OAI
