import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryResolution
import OAI.Algebra.Finitistic.Bimodule.BimoduleBarTensorComparison

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedBarBimodule
open SelectedOrdinaryAlgebra

/-- The action presentation of X used by the generic native/bar comparison. -/
abbrev comparisonX := BimoduleBarComparison.Actions ℂ D SelectedOrdinaryResolution.target

/-- Recover exactly the original right action of the constructed ordinary X. -/
def rightEquiv : comparisonX ≃ₗ[Dᵐᵒᵖ] X :=
  RetainedBimodule.rightEquiv ℂ D D X

/-- The same identification preserves the original outside left D-action. -/
theorem left_action (d : D) (x : comparisonX) : rightEquiv (d • x) = d • rightEquiv x :=
  RetainedBimodule.rightEquiv_left ℂ D D X d x

def leftEquiv : comparisonX ≃ₗ[D] X where
  toFun := rightEquiv
  invFun := rightEquiv.symm
  left_inv := rightEquiv.left_inv
  right_inv := rightEquiv.right_inv
  map_add' := rightEquiv.map_add
  map_smul' := left_action

theorem right_action (d : Dᵐᵒᵖ) (x : comparisonX) :
    leftEquiv (d • x) = d • leftEquiv x := rightEquiv.map_smul d x
end LittleFinitistic.SelectedBarBimodule

end

end OAI
