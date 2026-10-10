import OAI.Algebra.Finitistic.Ordinary.OrdinaryXResolution
import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalForget
import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalSingle
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRetainedCongruence

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

/-- The actual ordinary X, represented as a genuine D-bimodule. -/
abbrev ordinaryXObject : ModuleCat.{u} ((AlgebraD k l B) ⊗[k] (AlgebraD k l B)ᵐᵒᵖ) :=
  RetainedBimodule.object k (AlgebraD k l B) (AlgebraD k l B) (BimoduleX P a l)

def recoveredObjectIso : OffDiagonal.object k B (B ⊗[k] ChainAlgebra k l)
    (ordinaryOObject P a l) (TensorResolution.bimoduleTerminalObject k B l) ≅ ordinaryXObject P a l := by
  let eO := RetainedBimodule.rightEquiv k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l)
  let eT := RetainedBimodule.rightEquiv k B (B ⊗[k] ChainAlgebra k l) (TerminalTensor B)
  let e := OffDiagonal.congr eO eT
  have he (d : AlgebraD k l B) x : e (d • x) = d • e x := by
    apply Prod.ext
    · exact RetainedBimodule.rightEquiv_left k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) d.2 x.1
    · exact RetainedBimodule.rightEquiv_left k B (B ⊗[k] ChainAlgebra k l) (TerminalTensor B) d.1 x.2
  exact (RetainedBimodule.congr (k := k) e he).toModuleIso

/-- The previous component target is exactly X in degree zero, with both D-actions. -/
def targetIso : target P a l ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj (ordinaryXObject P a l) :=
  OffDiagonal.singleIso k B (B ⊗[k] ChainAlgebra k l) (ordinaryOObject P a l)
    (TensorResolution.bimoduleTerminalObject k B l) ≪≫
    (HomologicalComplex.single _ (.up ℤ) 0).mapIso (recoveredObjectIso P a l)

def augmentationToX : complex P a l ⟶
    (HomologicalComplex.single _ (.up ℤ) 0).obj (ordinaryXObject P a l) :=
  augmentation P a l ≫ (targetIso P a l).hom

/-- The actual bounded right-projective complex augments quasi-isomorphically to X. -/
theorem augmentationToX_quasiIso : QuasiIso (augmentationToX P a l) := by
  have := TensorResolution.integerBimoduleAugmentation_quasiIso k B l
  have : QuasiIso (augmentation P a l) := OffDiagonal.complexMap_quasiIso k B (B ⊗[k] ChainAlgebra k l)
    (𝟙 (ordinaryOComplex P a l)) (TensorResolution.integerBimoduleAugmentation k B l)
  unfold augmentationToX
  infer_instance
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
