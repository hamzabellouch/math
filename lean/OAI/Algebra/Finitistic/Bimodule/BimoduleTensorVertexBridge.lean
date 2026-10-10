import OAI.Algebra.Finitistic.Rectification.LeftVertexHomology
import OAI.Algebra.Finitistic.Tensor.BalancedVertexFunctor
import OAI.Algebra.Finitistic.Bimodule.BimoduleTensorUnderlying

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleTensorVertexBridge
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

/-- The full B-valued tensor functor has exactly the previously constructed
vertex spaces, with scalar restriction accounted for explicitly. -/
def equiv (e : B) (M : ModuleCat.{u} (Enveloping k B)) :
    (LeftVertexHomology.vertex k B e).obj ((BimoduleBalancedTensor.functor k B N).obj M) ≃ₗ[k]
      BalancedVertexFunctor.Space k B e N M where
  toFun x := ⟨x.val, (VertexFunctor.mem_fixed (algebraMap k B) e (LeftVertexHomology.scalar_commute k B e)
      ((BimoduleBalancedTensor.functor k B N).obj M) x.val).1 x.property⟩
  invFun x := ⟨x.val, (VertexFunctor.mem_fixed (algebraMap k B) e (LeftVertexHomology.scalar_commute k B e)
      ((BimoduleBalancedTensor.functor k B N).obj M) x.val).2 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := Subtype.ext (BimoduleBalancedTensor.algebraMap_smul k B M N c x.val)

/-- All induced differential and module maps are retained by the comparison. -/
def comparison (e : B) : BimoduleBalancedTensor.functor k B N ⋙
    LeftVertexHomology.vertex k B e ≅ BalancedVertexFunctor.functor k B e N :=
  NatIso.ofComponents (fun M => (equiv k B N e M).toModuleIso) (by
    intro M M' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl)

/-- An actual chain comparison with the vertex of the full B-module tensor complex. -/
def complexIso (e : B) (P : BiComplex k B) :
    (((LeftVertexHomology.vertex k B e).mapHomologicalComplex (.up ℤ)).obj
      (((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (((BalancedVertexFunctor.functor k B e N).mapHomologicalComplex (.up ℤ)).obj P) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (comparison k B N e).app (P.X n))
    (fun n m _ => ((comparison k B N e).hom.naturality (P.d n m)).symm)
end LittleFinitistic.BimoduleTensorVertexBridge

end

end OAI
