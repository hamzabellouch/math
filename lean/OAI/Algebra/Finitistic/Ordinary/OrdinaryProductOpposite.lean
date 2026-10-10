import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductSecondDimension
import Mathlib.Algebra.Algebra.Opposite

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

/-- The opposite of the actual product ring is the product of the two opposite rings. -/
def oppositeEquiv : (L × R)ᵐᵒᵖ ≃+* Lᵐᵒᵖ × Rᵐᵒᵖ where
  toFun x := (MulOpposite.op x.unop.1,MulOpposite.op x.unop.2)
  invFun x := MulOpposite.op (x.1.unop,x.2.unop)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

abbrev oppositeModule (M : ModuleCat.{v} (L × R)ᵐᵒᵖ) : ModuleCat.{v} (Lᵐᵒᵖ × Rᵐᵒᵖ) :=
  (ModuleCat.restrictScalars (oppositeEquiv L R).symm.toRingHom).obj M

attribute [local instance] RingHomInvPair.of_ringEquiv

def oppositeModuleEquiv (M : ModuleCat.{v} (L × R)ᵐᵒᵖ) :
    M ≃ₛₗ[RingHomClass.toRingHom (oppositeEquiv L R)] oppositeModule L R M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Small.{v} L] [Small.{v} R]

theorem opposite_product_module_bound (n : ℕ)
    (hL : ∀ M : ModuleCat.{v} Lᵐᵒᵖ, projectiveDimension M ≤ (n : ℕ))
    (hR : ∀ M : ModuleCat.{v} Rᵐᵒᵖ, projectiveDimension M ≤ (n : ℕ))
    (M : ModuleCat.{v} (L × R)ᵐᵒᵖ) : projectiveDimension M ≤ (n : ℕ) := by
  let : Small.{v} Lᵐᵒᵖ := small_of_injective (@MulOpposite.unop_injective L)
  let : Small.{v} Rᵐᵒᵖ := small_of_injective (@MulOpposite.unop_injective R)
  let : Small.{v} (L × R)ᵐᵒᵖ := small_of_injective (@MulOpposite.unop_injective (L × R))
  rw [ModuleCat.projectiveDimension_eq_of_semiLinearEquiv (oppositeEquiv L R) (oppositeModuleEquiv L R M)]
  exact product_module_bound Lᵐᵒᵖ Rᵐᵒᵖ n hL hR (oppositeModule L R M)
end LittleFinitistic.ProductModules

end

end OAI
