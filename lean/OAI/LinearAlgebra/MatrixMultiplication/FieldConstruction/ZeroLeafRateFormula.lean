import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.LeafRates

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldZeroLeafRates

open MatrixMultiplication.Foundation AllFieldParameters
open scoped BigOperators

def fourRate (t : Shape) : ℝ :=
  finiteEntropy (fun s : PairSlot => (zeroPairLaw t s.1 s.2 : ℝ)) +
    ∑ s : PairSlot, (zeroPairLaw t s.1 s.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 : ℕ)

end MatrixMultiplication.AllFieldZeroLeafRates

end

end OAI
