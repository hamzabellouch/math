import OAI.Analysis.MutuallyUnbiased.Fourier.FourierTheorem
import OAI.Analysis.MutuallyUnbiased.Tao.TaoCompleteFamily
import OAI.Analysis.MutuallyUnbiased.MixedMoments.MixedAlpha

namespace OAI

noncomputable section

namespace MUB6

theorem complete_family_fourier_zero (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    AllTransitionsFourierZero B := by
  intro r s
  rcases exact_dichotomy (relativeMatrix_isHadamard B hB r s) with hz | hs
  · exact hz
  · exact (complete_family_square_not_hadamard B hB r s hs).elim

end MUB6

end

end OAI
