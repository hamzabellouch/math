import Mathlib
import OAI.Algebra.Finitistic.Main
import OAI.Algebra.FinitisticAsymmetry.Transport.DiagramMaps
import OAI.Algebra.FinitisticAsymmetry.Asymmetry
import OAI.Algebra.FinitisticAsymmetry.Augmentation.Directed
import OAI.Algebra.FinitisticAsymmetry.Augmentation.SplitBasic

namespace OAI

section
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.SelectedBasic
open SelectedOrdinaryAlgebra SelectedFixedDiagram QuadraticEncoding
open OrdinarySimulation SplitBasic

def baseSystem := ThreeVertexAlgebra.directedSystem (composition P)
def chainSystem := ChainAlgebra.directedSystem ℂ length
def tensorSystem := TensorDirected.directedSystem baseSystem chainSystem
abbrev Vertices := Sum baseSystem.Vertices tensorSystem.Vertices

def diagonalAugmentation : D →ₐ[ℂ] (Vertices → ℂ) :=
  productAugmentation baseSystem.augmentation tensorSystem.augmentation
lemma diagonal_surjective : Function.Surjective diagonalAugmentation :=
  product_surjective _ _ baseSystem.augmentation_surjective tensorSystem.augmentation_surjective
lemma diagonal_ker_nilpotent :
    ∃ n : ℕ, (RingHom.ker diagonalAugmentation.toRingHom)^n = ⊥ :=
  product_ker_nilpotent _ _ baseSystem.augmentation_ker_nilpotent tensorSystem.augmentation_ker_nilpotent

def augmentationA : A →ₐ[ℂ] (Vertices → ℂ) :=
  squareZeroAugmentation (M := X) diagonalAugmentation
lemma augmentationA_surjective : Function.Surjective augmentationA :=
  squareZero_surjective _ diagonal_surjective
lemma augmentationA_ker_nilpotent :
    ∃ n : ℕ, (RingHom.ker augmentationA.toRingHom)^n = ⊥ :=
  squareZero_ker_nilpotent _ diagonal_ker_nilpotent

def augmentationC : Aᵐᵒᵖ →ₐ[ℂ] (Vertices → ℂ) := oppositeAugmentation augmentationA
lemma augmentationC_surjective : Function.Surjective augmentationC :=
  opposite_surjective _ augmentationA_surjective
lemma augmentationC_ker_nilpotent :
    ∃ n : ℕ, (RingHom.ker augmentationC.toRingHom)^n = ⊥ :=
  opposite_ker_nilpotent _ augmentationA_ker_nilpotent
end LittleFinitistic.SelectedBasic

namespace LittleFinitistic

theorem extreme_left_right_asymmetry :
    ∃ (Λ : Type) (_ : Ring Λ) (_ : Algebra ℂ Λ),
      FiniteDimensional ℂ Λ ∧
      littleFinitisticDimension Λ = ⊤ ∧ bigFinitisticDimension Λ = ⊤ ∧
      littleFinitisticDimension Λᵐᵒᵖ = 0 ∧ bigFinitisticDimension Λᵐᵒᵖ = 0 ∧
      ¬ InjectivesGenerate Λ ∧ InjectivesGenerate Λᵐᵒᵖ := by
  classical
  let Λ := AsymmetryConstruction.Lambda SelectedBasic.augmentationC
  refine ⟨Λ, inferInstance, inferInstance, ?_⟩
  exact AsymmetryConstruction.all_clauses SelectedBasic.augmentationC
    SelectedBasic.augmentationC_surjective SelectedBasic.augmentationC_ker_nilpotent
    Main.infinite_littleFinitisticDimension
end LittleFinitistic

end
end

end OAI
