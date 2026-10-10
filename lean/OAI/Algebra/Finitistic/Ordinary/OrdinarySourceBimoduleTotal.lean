import OAI.Algebra.Finitistic.Ordinary.OrdinaryGenuineBimoduleComparison
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTotalAssociativity
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTotalCongruence
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorTotalAcyclic

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
variable (b : ℤ) (hb : a+(l:ℤ)=b)
variable (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The source signed total comparison for every Z, with the actual outside B-action retained. -/
def sourceBimoduleTotalComparison :
    BimoduleComplexTensor.total k B (B ⊗[k] ChainAlgebra k l)
      (TensorResolution.integerBimoduleComplex k B l)
      (middleLeftComplex k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) Z)
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) ≅
    BimoduleComplexTensor.total k B B (P⟦b⟧) Z
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) :=
  (BimoduleComplexTensor.totalAssociativityIso k B (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l)
    (TensorResolution.integerBimoduleComplex k B l) Z
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)).symm ≪≫
  BimoduleComplexTensor.totalRightIso k B B (genuineSourceShiftComparison P a l b hb hP) Z
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)
end LittleFinitistic.OrdinarySimulation

end

end OAI
