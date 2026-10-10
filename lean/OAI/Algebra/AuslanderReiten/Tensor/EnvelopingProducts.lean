import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBimodule
import Mathlib.Algebra.Module.Projective

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.EnvelopingBimodule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))

def prodRightEquiv : EnvelopingBimodule k R (ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (M × N)) ≃ₗ[Rᵐᵒᵖ]
    EnvelopingBimodule k R M × EnvelopingBimodule k R N where
  toFun x := (⟨x.value.1⟩, ⟨x.value.2⟩)
  invFun x := ⟨(x.1.value, x.2.value)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem prod_right_projective
    [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M)]
    [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R N)] :
    Module.Projective Rᵐᵒᵖ
      (EnvelopingBimodule k R (ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (M × N))) :=
  Module.Projective.of_equiv (prodRightEquiv M N).symm

end ArExplicit.EnvelopingBimodule

end

end OAI
