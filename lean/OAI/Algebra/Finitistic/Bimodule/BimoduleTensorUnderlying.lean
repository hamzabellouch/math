import OAI.Algebra.Finitistic.Bimodule.BimoduleTensorFunctor

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleBalancedTensor
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

/-- Forgetting the actual left B action gives exactly the original balanced tensor vector space. -/
def underlyingEquiv (M : ModuleCat.{u} (Enveloping k B)) :
    (ModuleCat.restrictScalars (algebraMap k B)).obj ((functor k B N).obj M) ≃ₗ[k]
      (BalancedTensor.tensorFunctor k B N).obj ((forgetRight k B).obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := algebraMap_smul k B M N c x

/-- The comparison is natural, retaining the actual underlying maps and differentials. -/
def underlyingComparison : functor k B N ⋙ ModuleCat.restrictScalars (algebraMap k B) ≅
    forgetRight k B ⋙ BalancedTensor.tensorFunctor k B N :=
  NatIso.ofComponents (fun M => (underlyingEquiv k B N M).toModuleIso) (by
    intros M M' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

/-- Finite input vector spaces give finite balanced tensor spaces. -/
instance finite (M : ModuleCat.{u} (Enveloping k B))
    [FiniteDimensional k (Input k B M)] [FiniteDimensional k N] :
    FiniteDimensional k (Tensor k B M N) := by
  dsimp [Tensor]
  infer_instance
end LittleFinitistic.BimoduleBalancedTensor

end

end OAI
