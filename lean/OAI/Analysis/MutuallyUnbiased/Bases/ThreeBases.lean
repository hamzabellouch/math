import OAI.Analysis.MutuallyUnbiased.Bases.Tensor
import OAI.Analysis.MutuallyUnbiased.Bases.SmallMatrices

namespace OAI

/-! Explicit mutually unbiased bases from two- and three-dimensional unitary matrices. -/

theorem MUB6.three_mutually_unbiased_bases : MUB6.Attainable 3 :=
  MUB6.ThreeTensor.attainable_three_of_small_matrices
    MUB6.ThreeSmall.A MUB6.ThreeSmall.B
    MUB6.ThreeSmall.A_gram MUB6.ThreeSmall.B_gram
    MUB6.ThreeSmall.A_cross_normSq MUB6.ThreeSmall.B_cross_normSq

end OAI
