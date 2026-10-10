import OAI.Algebra.Finitistic.Localization.TensorEvaluationFunctor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

/-- Termwise tensor evaluation on actual complexes, descended through chain homotopies. -/
def homotopyEvaluation :
    HomotopyCategory (ModuleCat.{w} Aᵐᵒᵖ) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{max w z} k) (ComplexShape.up ℤ) :=
  (tensorFunctor k A N).mapHomotopyCategory (ComplexShape.up ℤ)

instance homotopyEvaluationShift : (homotopyEvaluation.{u,v,w,z} k A N).CommShift ℤ :=
  inferInstanceAs (((tensorFunctor.{u,v,w,z} k A N).mapHomotopyCategory (ComplexShape.up ℤ)).CommShift ℤ)

instance homotopyEvaluationTriangulated : (homotopyEvaluation.{u,v,w,z} k A N).IsTriangulated :=
  inferInstanceAs (((tensorFunctor.{u,v,w,z} k A N).mapHomotopyCategory (ComplexShape.up ℤ)).IsTriangulated)
end LittleFinitistic.BalancedTensor

end

end OAI
