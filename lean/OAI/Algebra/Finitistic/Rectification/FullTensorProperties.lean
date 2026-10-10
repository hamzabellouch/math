import OAI.Algebra.Finitistic.Bimodule.BimoduleTensorUnderlying
import OAI.Algebra.Finitistic.Rectification.TotalFinite
import OAI.Algebra.Finitistic.Rectification.InducedRectification

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.FullTensorProperties
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- The tensor input's scalar structure agrees with the original bimodule's
scalar restriction through the two algebra homomorphisms. -/
def inputEquiv (M : ModuleCat.{u} (Enveloping k B)) :
    (forgetK k B).obj M ≃ₗ[k] BimoduleBalancedTensor.Input k B M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k (Enveloping k B) c) • (show M from x) =
      (BimoduleVertex.restriction k B (algebraMap k Bᵐᵒᵖ c)) • (show M from x)
    have h : BimoduleVertex.restriction k B (algebraMap k Bᵐᵒᵖ c) =
        algebraMap k (Enveloping k B) c := Algebra.TensorProduct.includeRight.commutes c
    rw [h]

variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

theorem finite (M : ModuleCat.{u} (Enveloping k B))
    [FiniteDimensional k ((forgetK k B).obj M)] [FiniteDimensional k N] :
    FiniteDimensional k ((ModuleCat.restrictScalars (algebraMap k B)).obj
      ((BimoduleBalancedTensor.functor k B N).obj M)) := by
  have : FiniteDimensional k (BimoduleBalancedTensor.Input k B M) :=
    Module.Finite.of_surjective (inputEquiv k B M).toLinearMap (inputEquiv k B M).surjective
  have : FiniteDimensional k ((BalancedTensor.tensorFunctor k B N).obj ((forgetRight k B).obj M)) :=
    inferInstanceAs (FiniteDimensional k (BimoduleBalancedTensor.Tensor k B M N))
  apply Module.Finite.of_surjective (BimoduleBalancedTensor.underlyingEquiv k B N M).symm.toLinearMap
    (BimoduleBalancedTensor.underlyingEquiv k B N M).symm.surjective

theorem bounded (P : BiComplex k B) (lo hi : ℤ)
    (h : ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) :
    ∀ n, n < lo ∨ hi < n → IsZero
      ((((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P).X n) := by
  intro n hn
  exact (BimoduleBalancedTensor.functor k B N).map_isZero (h n hn)
end LittleFinitistic.FullTensorProperties

end

end OAI
