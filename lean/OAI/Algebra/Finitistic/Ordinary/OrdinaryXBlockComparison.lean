import OAI.Algebra.Finitistic.Ordinary.OrdinaryXDerivedTensor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFirstBlockTotal
import OAI.Algebra.Finitistic.Ordinary.OrdinarySecondBlockTotal
import OAI.Algebra.Finitistic.Ordinary.OrdinarySingleTensorTotal
import OAI.Algebra.Finitistic.Ordinary.OrdinarySourceBimoduleTotal

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

/-- The first actual tensor application is exactly ordinary O tensor Z on the second block. -/
def firstBlockComparison (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    (tensorFunctor P a l).obj (BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l) Z) ≅
    BlockModule.secondComplex B (B ⊗[k] ChainAlgebra k l)
      (middleLeftComplex k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) Z) :=
  BlockTensor.firstTotalIso k B (B ⊗[k] ChainAlgebra k l) (ordinaryOComplex P a l)
    (TensorResolution.integerBimoduleComplex k B l) Z
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) ≪≫
  ((ProductModules.secondInflation B (B ⊗[k] ChainAlgebra k l)).mapHomologicalComplex (.up ℤ)).mapIso
    (SingleBimoduleTensor.totalIso k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) Z
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) (Fin.last l)
      (by simp [TensorResolution.finiteDegrees]))

/-- The second actual tensor application selects Q_T and retains first-block support. -/
def secondBlockComparison (Y : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)) ℤ) :
    (tensorFunctor P a l).obj (BlockModule.secondComplex B (B ⊗[k] ChainAlgebra k l) Y) ≅
    BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l)
      (BimoduleComplexTensor.total k B (B ⊗[k] ChainAlgebra k l) (TensorResolution.integerBimoduleComplex k B l) Y
        (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)) :=
  BlockTensor.secondTotalIso k B (B ⊗[k] ChainAlgebra k l) (ordinaryOComplex P a l)
    (TensorResolution.integerBimoduleComplex k B l) Y
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

/-- The complete actual chain-level square calculation, with the source support and outside action. -/
def squareComparison (b : ℤ) (hb : a+(l:ℤ)=b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    (tensorFunctor P a l).obj ((tensorFunctor P a l).obj (BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l) Z)) ≅
    BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l)
      (BimoduleComplexTensor.total k B B (P⟦b⟧) Z
        (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)) :=
  (tensorFunctor P a l).mapIso (firstBlockComparison P a l Z) ≪≫
  secondBlockComparison P a l (middleLeftComplex k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) Z) ≪≫
  ((ProductModules.firstInflation B (B ⊗[k] ChainAlgebra k l)).mapHomologicalComplex (.up ℤ)).mapIso
    (sourceBimoduleTotalComparison P a l b hb hP Z)
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
