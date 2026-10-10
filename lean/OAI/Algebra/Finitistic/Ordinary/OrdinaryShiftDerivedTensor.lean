import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleDerivedTensor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRightProjective
import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftSign

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (b : ℤ) (l : ℕ)
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]

instance shifted_right_projective (n : ℤ) : Module.Projective Bᵐᵒᵖ
    (ComplexTensor.rightTerm k B (BimoduleComplexTensor.rightComplex k B B (P⟦b⟧)) n) :=
  inferInstanceAs (Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X (n+b)))

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- The native derived tensor functor computed by the source's actual bounded P[b]. -/
def shiftedDerivedTensor : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  BimoduleComplexTensor.derivedTotal k B B (P⟦b⟧)
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

def shiftedDerivedTensorComparison : DerivedCategory.Q ⋙ shiftedDerivedTensor P b l ≅
    BimoduleComplexTensor.totalFunctor k B B (P⟦b⟧)
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) ⋙ DerivedCategory.Q :=
  BimoduleComplexTensor.derivedTotalComparison k B B (P⟦b⟧)
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

omit [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]
  [HasDerivedCategory.{u+1} (ModuleCat.{u} B)] in
theorem shifted_support (a : ℤ) (hb : a+(l:ℤ)=b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) (n : ℤ) (hn : n < -(l:ℤ) ∨ 0 < n) :
    IsZero ((P⟦b⟧).X n) := by
  change IsZero (P.X (n+b))
  apply hP
  omega
end LittleFinitistic.OrdinarySimulation

end

end OAI
