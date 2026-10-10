import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexConstantPolynomialKernel
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexLabelHierarchySeparation

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PolynomialLocalConstruction

open Tensor

def poolAuxiliaryApproximation (k : ℕ) :
    PolynomialApproximation (LabelHierarchySeparation.poolAuxiliaryTensor k)
      (LabelHierarchySeparation.poolAuxiliaryCost k) 0 0 :=
  PolynomialApproximation.ofRankAtMost _ _
    (LabelHierarchySeparation.poolAuxiliaryTensor_rankAtMost k)

end MatrixMultiplication.Foundation.PolynomialLocalConstruction

end

end OAI
