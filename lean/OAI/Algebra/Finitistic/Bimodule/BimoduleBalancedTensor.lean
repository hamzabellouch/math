import OAI.Algebra.Finitistic.Rectification.VertexTensorLinear
import OAI.Algebra.Finitistic.Localization.TensorEvaluationFunctor
import OAI.Algebra.Finitistic.Rectification.ColumnProperties

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleBalancedTensor
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B))
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

abbrev Input := BalancedTensor.ScalarModule k B ((forgetRight k B).obj M)
local instance inputEnveloping : Module (Enveloping k B) (Input k B M) :=
  inferInstanceAs (Module (Enveloping k B) M)

abbrev Tensor := BalancedTensor.Tensor k B (Input k B M) N

def inputAction (b : B) : Input k B M →ₗ[Bᵐᵒᵖ] Input k B M :=
  VertexFunctor.action (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B b)
    (BimoduleVertex.vertex_commute k B b) M

/-- The original left B action on a genuine bimodule descends through balancing over B. -/
def action : B →+* Module.End k (Tensor k B M N) where
  toFun b := BalancedTensor.mapLeft (k := k) N (inputAction k B M b)
  map_zero' := by
    apply BalancedTensor.ext
    intro m n
    change BalancedTensor.mk k B (Input k B M) N (((0 : B) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n = 0
    rw [TensorProduct.zero_tmul]
    have hz : (0 : Enveloping k B) • (m : M) = 0 := Module.zero_smul (R := Enveloping k B) m
    rw [hz]
    simp
  map_one' := by
    apply BalancedTensor.ext
    intro m n
    change BalancedTensor.mk k B (Input k B M) N (((1 : B) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n =
      BalancedTensor.mk k B (Input k B M) N m n
    rw [← Algebra.TensorProduct.one_def,one_smul]
  map_add' a b := by
    apply BalancedTensor.ext
    intro m n
    change BalancedTensor.mk k B (Input k B M) N (((a+b) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n =
      BalancedTensor.mk k B (Input k B M) N ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n +
      BalancedTensor.mk k B (Input k B M) N ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n
    rw [TensorProduct.add_tmul,add_smul]
    exact LinearMap.congr_fun ((BalancedTensor.mk k B (Input k B M) N).map_add _ _) n
  map_mul' a b := by
    apply BalancedTensor.ext
    intro m n
    change BalancedTensor.mk k B (Input k B M) N (((a*b) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n =
      BalancedTensor.mk k B (Input k B M) N
        ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M))) n
    rw [← mul_smul,Algebra.TensorProduct.tmul_mul_tmul,one_mul]

instance leftModule : Module B (Tensor k B M N) :=
  Module.compHom (Tensor k B M N) (action k B M N)

@[simp] theorem smul_mk (b : B) (m : Input k B M) (n : N) :
    b • BalancedTensor.mk k B (Input k B M) N m n =
      BalancedTensor.mk k B (Input k B M) N
        ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n := rfl
end LittleFinitistic.BimoduleBalancedTensor

end

end OAI
