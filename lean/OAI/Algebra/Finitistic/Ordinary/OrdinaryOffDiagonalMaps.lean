import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockBimodule
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRetainedBimodule

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable {L R O O' T T' : Type u} [Ring L] [Ring R]
variable [AddCommGroup O] [AddCommGroup O'] [AddCommGroup T] [AddCommGroup T']
variable [Module R O] [Module R O'] [Module L T] [Module L T']
variable [Module Lᵐᵒᵖ O] [Module Lᵐᵒᵖ O'] [Module Rᵐᵒᵖ T] [Module Rᵐᵒᵖ T']

/-- Actual component maps of the off-diagonal right product-ring module. -/
def map (f : O →ₗ[Lᵐᵒᵖ] O') (g : T →ₗ[Rᵐᵒᵖ] T') :
    OffDiagonal O T →ₗ[(L × R)ᵐᵒᵖ] OffDiagonal O' T' where
  toFun x := (f x.1,g x.2)
  map_add' left right := Prod.ext (f.map_add left.1 right.1) (g.map_add left.2 right.2)
  map_smul' d x := Prod.ext (f.map_smul (MulOpposite.op d.unop.1) x.1)
    (g.map_smul (MulOpposite.op d.unop.2) x.2)

/-- The same map retains the two prescribed left product-ring actions. -/
theorem map_left (f : O →ₗ[Lᵐᵒᵖ] O') (hf : ∀ (r : R) x, f (r • x) = r • f x)
    (g : T →ₗ[Rᵐᵒᵖ] T') (hg : ∀ (s : L) x, g (s • x) = s • g x)
    (d : L × R) (x : OffDiagonal O T) :
    map f g (d • x) = d • map f g x :=
  Prod.ext (hf d.2 x.1) (hg d.1 x.2)
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
