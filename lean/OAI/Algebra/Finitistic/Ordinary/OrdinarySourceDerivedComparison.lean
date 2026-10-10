import OAI.Algebra.Finitistic.Ordinary.OrdinarySourceResolutionModels
import OAI.Algebra.Finitistic.Ordinary.OrdinaryDerivedSquareComparison

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

section Bimodule
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (Enveloping k B))]

/-- The source's resolved T tensor O comparison in the native derived category of genuine B-bimodules.
Its left operand includes the actual bounded right-BC-projective resolution and augmentation to T. -/
def resolvedBimoduleComparison :
    (TensorResolution.resolutionModel k B l).tensorOrdinary B (BimoduleO P a l) ≅
      DerivedCategory.Q.obj (P⟦b⟧) :=
  DerivedCategory.Q.mapIso (genuineSourceShiftComparison P a l b hb hP)
end Bimodule

variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (AlgebraD k l B))]

/-- The source's native derived square with both tensor functors tied to their certified full-support models. -/
def resolvedSquareComparison (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    (XResolution.resolutionModel P a l).toFiniteProjectiveBimoduleComplex.derivedTensor.obj
      ((XResolution.resolutionModel P a l).toFiniteProjectiveBimoduleComplex.derivedTensor.obj
        ((BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj (DerivedCategory.Q.obj Z))) ≅
    (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj
      ((shiftedResolutionModel P a l b hb hP).derivedTensor.obj (DerivedCategory.Q.obj Z)) :=
  XResolution.derivedSquareComparison P a l b hb hP Z
end LittleFinitistic.OrdinarySimulation

end

end OAI
