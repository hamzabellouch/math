import OAI.Algebra.Finitistic.Ordinary.OrdinaryXAugmentation
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleDerivedTensor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]

instance rightTerm_projective (n : ℤ) : Module.Projective (AlgebraD k l B)ᵐᵒᵖ
    (ComplexTensor.rightTerm k (AlgebraD k l B)
      (BimoduleComplexTensor.rightComplex k (AlgebraD k l B) (AlgebraD k l B) (complex P a l)) n) :=
  right_projective P a l n

/-- Tensor with the actual right-projective Q_X on arbitrary input complexes of D-modules. -/
abbrev tensorFunctor := BimoduleComplexTensor.totalFunctor k (AlgebraD k l B) (AlgebraD k l B)
  (complex P a l) (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

theorem tensorFunctor_quasiIso {Z Z' : CochainComplex (ModuleCat.{u} (AlgebraD k l B)) ℤ}
    (f : Z ⟶ Z') [QuasiIso f] : QuasiIso ((tensorFunctor P a l).map f) :=
  BimoduleComplexTensor.totalFunctor_quasiIso k (AlgebraD k l B) (AlgebraD k l B)
    (complex P a l) (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) f

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (AlgebraD k l B))]

/-- The derived endofunctor obtained from the actual bounded resolution of X. -/
def derivedTensor : DerivedCategory (ModuleCat.{u} (AlgebraD k l B)) ⥤
    DerivedCategory (ModuleCat.{u} (AlgebraD k l B)) :=
  BimoduleComplexTensor.derivedTotal k (AlgebraD k l B) (AlgebraD k l B) (complex P a l)
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

def derivedTensorComparison : DerivedCategory.Q ⋙ derivedTensor P a l ≅
    tensorFunctor P a l ⋙ DerivedCategory.Q :=
  BimoduleComplexTensor.derivedTotalComparison k (AlgebraD k l B) (AlgebraD k l B) (complex P a l)
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
