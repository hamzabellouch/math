import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBetaTransfer
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluatedFreeCoordinate
import OAI.Algebra.AuslanderReiten.Homology.CoefficientComplexValues
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarPure

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)

theorem evaluatedFreeCoordinate_eq :
    evaluatedFreeCoordinate q hq =
      (simpleOrdinaryBarIso q).hom.f 0 ≫ (simpleCoefficientComplexIso q).hom.f 0 ≫
        ExternalBalanced.totalFreeEvaluation k (T k q) (T k q)
          (Resolution.Simple q) (Resolution.Simple q)
          (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq) := by
  rw [evaluatedFreeCoordinate, simpleNativeBarIso_hom_f]
  erw [Category.assoc, Category.assoc]

end ArExplicit.T

end

end OAI
