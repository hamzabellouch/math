import OAI.Algebra.Finitistic.Ordinary.OrdinaryRetainedBimodule
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.RetainedBimodule
universe u
variable (k S A M : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]

abbrev object : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ) := ModuleCat.of _ (RetainedBimodule k S A M)

/-- Recover the exact original right action after packaging the ordinary bimodule. -/
def rightEquiv : BimoduleCoefficients k S A (object k S A M) ≃ₗ[Aᵐᵒᵖ] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change action k S A M ((1:S) ⊗ₜ[k] r) x = _
    unfold action
    erw [Algebra.TensorProduct.lift_tmul]
    change (1:S) • (r • (show M from x)) = r • (show M from x)
    exact one_smul _ _

theorem rightEquiv_left (s : S) (x : BimoduleCoefficients k S A (object k S A M)) :
    rightEquiv k S A M (s • x) = s • rightEquiv k S A M x := by
  change action k S A M (s ⊗ₜ[k] (1:Aᵐᵒᵖ)) x = _
  unfold action
  erw [Algebra.TensorProduct.lift_tmul]
  change s • ((1:Aᵐᵒᵖ) • (show M from x)) = s • (show M from x)
  rw [one_smul]

/-- Recover the exact original scalar module after retaining both actions. -/
def scalarEquiv : (ModuleCat.restrictScalars (algebraMap k (S ⊗[k] Aᵐᵒᵖ))).obj
    (object k S A M) ≃ₗ[k] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    have h (y : RetainedBimodule k S A M) :
        (algebraMap k (S ⊗[k] Aᵐᵒᵖ) r) • y = r • y := algebraMap_smul _ r y
    exact h x
end LittleFinitistic.RetainedBimodule

end

end OAI
