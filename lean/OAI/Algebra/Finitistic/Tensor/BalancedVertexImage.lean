import OAI.Algebra.Finitistic.Bimodule.BimoduleTensorFunctor
import OAI.Algebra.Finitistic.Localization.AdditiveSplitImage
import OAI.Algebra.Finitistic.Tensor.IdempotentTensor

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BalancedVertexImage
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B)) (e : B) (he : e*e=e)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

local instance originalRightModule : Module Bᵐᵒᵖ M :=
  Module.compHom M (BimoduleVertex.restriction k B)

abbrev V := (BimoduleVertex.functor k B e).obj M
abbrev W := (forgetRight k B).obj M
abbrev F := BalancedTensor.tensorFunctor k B N

def inclusion : V k B M e ⟶ W k B M := ModuleCat.ofHom
  (VertexFunctor.inclusion (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B e)
    (BimoduleVertex.vertex_commute k B e) M)
def projection : W k B M ⟶ V k B M e := ModuleCat.ofHom
  (VertexFunctor.projection (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B e)
    (BimoduleVertex.vertex_idempotent k B e he) (BimoduleVertex.vertex_commute k B e) M)

theorem split : inclusion k B M e ≫ projection k B M e he = 𝟙 _ :=
  ModuleCat.hom_ext (VertexFunctor.projection_inclusion (BimoduleVertex.restriction k B)
    (BimoduleVertex.vertex k B e) (BimoduleVertex.vertex_idempotent k B e he)
    (BimoduleVertex.vertex_commute k B e) M)

theorem projector : ((F k B N).map (projection k B M e he ≫ inclusion k B M e)).hom =
    BimoduleBalancedTensor.action k B M N e := by
  apply BalancedTensor.ext
  intro m n
  rfl

/-- The image of the original vertex projector after tensoring is the actual left vertex. -/
def fixedEquiv :
    AdditiveSplitImage.fixed (F k B N) (inclusion k B M e) (projection k B M e he) ≃ₗ[k]
      IdempotentTensor.leftSpace (k := k) e (BimoduleBalancedTensor.Tensor k B M N) where
  toFun x := ⟨x.val,by
    change BimoduleBalancedTensor.action k B M N e x.val = x.val
    rw [← projector k B M e he N]
    exact (AdditiveSplitImage.mem_fixed _ _ _ x.val).1 x.property⟩
  invFun x := ⟨x.val,by
    exact (AdditiveSplitImage.mem_fixed (F k B N) (inclusion k B M e)
      (projection k B M e he) x.val).2
        ((LinearMap.congr_fun (projector k B M e he N) x.val).trans x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Vertex extraction commutes with actual balanced tensoring, without a flatness assumption. -/
def equiv : (F k B N).obj (V k B M e) ≃ₗ[k]
    IdempotentTensor.leftSpace (k := k) e (BimoduleBalancedTensor.Tensor k B M N) :=
  (AdditiveSplitImage.equiv (F k B N) (inclusion k B M e) (projection k B M e he)
    (split k B M e he)).trans (fixedEquiv k B M e he N)

@[simp] theorem equiv_apply_val (x : (F k B N).obj (V k B M e)) :
    (equiv k B M e he N x).val = ((F k B N).map (inclusion k B M e)).hom x := rfl
end LittleFinitistic.BalancedVertexImage

end

end OAI
