import OAI.Algebra.Finitistic.Ordinary.OrdinaryRetainedRestriction
import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalMaps

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RetainedBimodule
universe u
variable {k S A M N : Type u} [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module S N] [Module Aᵐᵒᵖ N]
  [IsScalarTower k S N] [IsScalarTower k Aᵐᵒᵖ N] [SMulCommClass S Aᵐᵒᵖ N]

/-- An actual right-linear, left-equivariant equivalence retains both actions. -/
def congr (f : M ≃ₗ[Aᵐᵒᵖ] N) (hf : ∀ (s : S) x, f (s • x) = s • f x) :
    RetainedBimodule k S A M ≃ₗ[S ⊗[k] Aᵐᵒᵖ] RetainedBimodule k S A N where
  __ := map (k := k) f.toLinearMap hf
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv
end LittleFinitistic.RetainedBimodule
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable {L R O O' T T' : Type u} [Ring L] [Ring R]
variable [AddCommGroup O] [AddCommGroup O'] [AddCommGroup T] [AddCommGroup T']
variable [Module Lᵐᵒᵖ O] [Module Lᵐᵒᵖ O'] [Module Rᵐᵒᵖ T] [Module Rᵐᵒᵖ T']

def congr (f : O ≃ₗ[Lᵐᵒᵖ] O') (g : T ≃ₗ[Rᵐᵒᵖ] T') :
    OffDiagonal O T ≃ₗ[(L × R)ᵐᵒᵖ] OffDiagonal O' T' where
  toFun x := (f x.1,g x.2)
  invFun x := (f.symm x.1,g.symm x.2)
  left_inv x := Prod.ext (f.left_inv x.1) (g.left_inv x.2)
  right_inv x := Prod.ext (f.right_inv x.1) (g.right_inv x.2)
  map_add' left right := Prod.ext (f.map_add left.1 right.1) (g.map_add left.2 right.2)
  map_smul' d x := Prod.ext (f.map_smul (MulOpposite.op d.unop.1) x.1)
    (g.map_smul (MulOpposite.op d.unop.2) x.2)
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
