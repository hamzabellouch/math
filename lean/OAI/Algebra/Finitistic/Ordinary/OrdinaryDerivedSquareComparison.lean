import OAI.Algebra.Finitistic.Ordinary.OrdinaryXBlockComparison
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockDerived
import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftDerivedTensor

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
variable (b : ℤ) (hb : a+(l:ℤ)=b)
variable (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (AlgebraD k l B))]

/-- The actual native derived square comparison on every complex Z, with first-block support.
Both tensor functors are the localization lifts of their verified bounded projective models. -/
def derivedSquareComparison (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    (derivedTensor P a l).obj ((derivedTensor P a l).obj
      ((BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj (DerivedCategory.Q.obj Z))) ≅
    (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj
      ((shiftedDerivedTensor P b l).obj (DerivedCategory.Q.obj Z)) :=
  (derivedTensor P a l).mapIso ((derivedTensor P a l).mapIso
    ((BlockModule.derivedFirstComparison B (B ⊗[k] ChainAlgebra k l)).app Z)) ≪≫
  (derivedTensor P a l).mapIso ((derivedTensorComparison P a l).app
    (BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l) Z)) ≪≫
  (derivedTensorComparison P a l).app
    ((tensorFunctor P a l).obj (BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l) Z)) ≪≫
  DerivedCategory.Q.mapIso (squareComparison P a l b hb hP Z) ≪≫
  ((BlockModule.derivedFirstComparison B (B ⊗[k] ChainAlgebra k l)).app
    (BimoduleComplexTensor.total k B B (P⟦b⟧) Z
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l))).symm ≪≫
  (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).mapIso
    ((shiftedDerivedTensorComparison P b l).app Z).symm
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
