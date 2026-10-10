import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleCoefficients
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTwoSidedTensor
import Mathlib.Algebra.Homology.Additive

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic
universe u
variable (k S A T N : Type u) [Field k] [Ring S] [Ring A] [Ring T]
  [Algebra k S] [Algebra k A] [Algebra k T]
variable [AddCommGroup N] [Module k N] [Module A N] [Module T N]
  [IsScalarTower k A N] [IsScalarTower k T N] [SMulCommClass T A N]

/-- Actual ordinary tensor with a fixed bimodule, preserving both outside actions. -/
def bimoduleTensorFunctor : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ) ⥤ ModuleCat.{u} (S ⊗[k] T) where
  obj M := ModuleCat.of _ (TwoSidedTensor k A S T (BimoduleCoefficients k S A M) N)
  map f := ModuleCat.ofHom (TwoSidedTensor.map (T := T) (N := N)
    (BimoduleCoefficients.map k S A f) (BimoduleCoefficients.map_left k S A f))
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m n
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m n
    rfl

instance bimoduleTensorFunctor_additive : (bimoduleTensorFunctor k S A T N).Additive where
  map_add {M M'} {f g} := by
    dsimp only [bimoduleTensorFunctor]
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m n
    exact congrArg (fun h => h n)
      ((BalancedTensor.mk k A (BimoduleCoefficients k S A M') N).map_add (f.hom m) (g.hom m))
end LittleFinitistic

end

end OAI
