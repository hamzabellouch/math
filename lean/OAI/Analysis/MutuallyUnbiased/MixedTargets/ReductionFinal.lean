import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound59
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionFinalArithmetic

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem originalReductionEval (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Combination.eval MixedData.targetRows (numericVector B) MixedData.rawCombination =
      (37623398400 : ℝ) * Integer.Sparse.eval originalPolynomial (originalVector B) := by
  rw [← numericReductionEval, reducedMergeEval1917 B hB hF, originalReductionCheck]

end MUB6.Certificate.MixedTargetSemantics

end OAI
