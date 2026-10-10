import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleCoefficients

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic
universe u
/-- An ordinary bimodule packaged as a module over its actual tensor algebra. -/
def RetainedBimodule (_k _S _A M : Type u) := M
namespace RetainedBimodule
variable (k S A M : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]
instance : AddCommGroup (RetainedBimodule k S A M) := inferInstanceAs (AddCommGroup M)
instance : Module k (RetainedBimodule k S A M) := inferInstanceAs (Module k M)
instance : Module S (RetainedBimodule k S A M) := inferInstanceAs (Module S M)
instance : Module Aᵐᵒᵖ (RetainedBimodule k S A M) := inferInstanceAs (Module Aᵐᵒᵖ M)
instance : IsScalarTower k S (RetainedBimodule k S A M) := inferInstanceAs (IsScalarTower k S M)
instance : IsScalarTower k Aᵐᵒᵖ (RetainedBimodule k S A M) := inferInstanceAs (IsScalarTower k Aᵐᵒᵖ M)
instance : SMulCommClass S Aᵐᵒᵖ (RetainedBimodule k S A M) := inferInstanceAs (SMulCommClass S Aᵐᵒᵖ M)


def action : (S ⊗[k] Aᵐᵒᵖ) →ₐ[k] Module.End k (RetainedBimodule k S A M) :=
  show (S ⊗[k] Aᵐᵒᵖ) →ₐ[k] Module.End k M from
  Algebra.TensorProduct.lift (Algebra.lsmul k k M) (Algebra.lsmul k k M) (by
    intro s a
    ext m
    exact smul_comm s a (m : M))
instance : Module (S ⊗[k] Aᵐᵒᵖ) (RetainedBimodule k S A M) := Module.compHom _ (action k S A M).toRingHom
instance tower : IsScalarTower k (S ⊗[k] Aᵐᵒᵖ) (RetainedBimodule k S A M) where
  smul_assoc r x m := by
    change action k S A M (r • x) m = r • action k S A M x m
    rw [map_smul]
    rfl

variable {k S A M} {M' : Type u}
variable [AddCommGroup M'] [Module k M'] [Module S M'] [Module Aᵐᵒᵖ M']
  [IsScalarTower k S M'] [IsScalarTower k Aᵐᵒᵖ M'] [SMulCommClass S Aᵐᵒᵖ M']

def map (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m) :
    RetainedBimodule k S A M →ₗ[S ⊗[k] Aᵐᵒᵖ] RetainedBimodule k S A M' where
  __ := f.toAddHom
  map_smul' x m := by
    change f (action k S A M x m) = action k S A M' x (f m)
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      change f (s • (a • (m : M))) = s • (a • f (m : M))
      exact (hf s (a • (m : M))).trans (congrArg (s • ·) (f.map_smul a (m : M)))
    | add x y hx hy =>
      rw [map_add, map_add]
      exact (f.map_add _ _).trans (congrArg₂ (· + ·) hx hy)
end RetainedBimodule
end LittleFinitistic

end

end OAI
