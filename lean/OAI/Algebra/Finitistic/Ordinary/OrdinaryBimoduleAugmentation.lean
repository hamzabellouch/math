import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorBimoduleResolution
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRestrictionHomology

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

abbrev bimoduleTerminal := RetainedBimodule k B (B ⊗[k] ChainAlgebra k l) (TerminalTensor B)
abbrev bimoduleTerminalObject : ModuleCat.{u} (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) :=
  ModuleCat.of _ (bimoduleTerminal k B l)

def bimoduleAugmentationHom : (bimoduleComplex k B l).X l ⟶ bimoduleTerminalObject k B l :=
  ModuleCat.ofHom (RetainedBimodule.map (k := k) (S := B) (A := B ⊗[k] ChainAlgebra k l)
    (augmentation k B l) (augmentation_left k B l))

/-- The actual augmentation of the genuine finite bimodule resolution. -/
def bimoduleAugmentationMap : bimoduleComplex k B l ⟶
    (HomologicalComplex.single _ (.up ℕ) l).obj (bimoduleTerminalObject k B l) :=
  HomologicalComplex.mkHomToSingle (bimoduleAugmentationHom k B l) (by
    intro i hi
    change i+1=l at hi
    subst l
    change CochainComplex.of.d _ _ i (i+1) ≫ bimoduleAugmentationHom k B (i+1) = 0
    erw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f x) (augmentation_comp k B i))

def forgetBimoduleTerminal : (forgetBimodule k B l).obj (bimoduleTerminalObject k B l) ≅
    ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) := by
  let e : (forgetBimodule k B l).obj (bimoduleTerminalObject k B l) ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
      TerminalTensor B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (1:B) * (TerminalTensor.value B x * terminalAugmentation k B l r.unop) =
          TerminalTensor.value B x * terminalAugmentation k B l r.unop
        exact one_mul _ }
  exact e.toModuleIso

def forgetAugmentationTargetIso :
    ((forgetBimodule k B l).mapHomologicalComplex (.up ℕ)).obj
      ((HomologicalComplex.single _ (.up ℕ) l).obj (bimoduleTerminalObject k B l)) ≅
    (HomologicalComplex.single _ (.up ℕ) l).obj
      (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) :=
  (HomologicalComplex.singleMapHomologicalComplex (forgetBimodule k B l) (.up ℕ) l).app
      (bimoduleTerminalObject k B l) ≪≫
    (HomologicalComplex.single _ (.up ℕ) l).mapIso (forgetBimoduleTerminal k B l)
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
