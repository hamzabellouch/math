import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBimodule
import OAI.Algebra.AuslanderReiten.Modules.TwistedBimodule

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
variable [SMulCommClass k R M] [SMulCommClass k Rᵐᵒᵖ M]
variable [SMulCommClass R Rᵐᵒᵖ M]

def bimoduleEnvelopingRepresentation : R ⊗[k] Rᵐᵒᵖ →ₐ[k] Module.End k M :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k M) (Algebra.lsmul k k M) (by
    intro a b
    apply LinearMap.ext
    intro x
    exact smul_comm a b x)

@[instance_reducible] def bimoduleEnvelopingModule : Module (R ⊗[k] Rᵐᵒᵖ) M :=
  Module.compHom M (bimoduleEnvelopingRepresentation k R M).toRingHom

def bimoduleEnvelopingObject : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) :=
  letI := bimoduleEnvelopingModule k R M
  ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M

instance : Module k (bimoduleEnvelopingObject k R M) := inferInstanceAs (Module k M)

instance : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) (bimoduleEnvelopingObject k R M) :=
  IsScalarTower.of_algebraMap_smul (A := R ⊗[k] Rᵐᵒᵖ) fun a (x : bimoduleEnvelopingObject k R M) => by
    change bimoduleEnvelopingRepresentation k R M (algebraMap k (R ⊗[k] Rᵐᵒᵖ) a) x = a • x
    rw [AlgHom.commutes]
    rfl

omit [SMulCommClass k R M] [SMulCommClass k Rᵐᵒᵖ M] in
@[simp] theorem bimoduleEnveloping_smul (a : R) (b : Rᵐᵒᵖ) (x : bimoduleEnvelopingObject k R M) :
    (a ⊗ₜ[k] b) • x = a • (b • (show M from x)) := rfl

def bimoduleEnvelopingLeftEquiv :
    ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj
      (bimoduleEnvelopingObject k R M)) ≃ₗ[R] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change a • ((1 : Rᵐᵒᵖ) • (show M from x)) = a • (show M from x)
    rw [one_smul]

def bimoduleEnvelopingRightEquiv :
    ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj
      (bimoduleEnvelopingObject k R M)) ≃ₗ[Rᵐᵒᵖ] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (1 : R) • (a • (show M from x)) = a • (show M from x)
    rw [one_smul]

end ArExplicit

end

end OAI
