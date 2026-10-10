import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyAll
import OAI.Analysis.MutuallyUnbiased.MixedTargets.OriginalCollection
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionFinal
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Semantics

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

/-- The collected mixed polynomial is the genuine nonnegative Gram expression. -/
theorem originalGramIdentity (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval originalPolynomial (originalVector B) =
      GramNonnegative.sourceGram B := by
  rw [originalPolynomialEval]
  have h : (fun i => Integer.Sparse.eval (keyMomentRows i) (originalVector B)) =
      (fun i => 5 * GramNormalization.eval B (GramAssembly.key i)) :=
    funext fun i => (allKeyMoments B hB i).symm
  rw [h, Integer.Sparse.eval_mul_left]
  exact GramAssembly.interpretation B hB

/-- The exact integer target has the manuscript's Gram interpretation, including
both its factor of five and its common integer denominator. -/
theorem rawGramIdentity (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Combination.eval MixedData.targetRows (numericVector B) MixedData.rawCombination =
      (MixedData.denominator : ℝ) * GramNonnegative.sourceGram B := by
  rw [originalReductionEval B hB hF, originalGramIdentity B hB]
  rfl

end MUB6.Certificate.MixedTargetSemantics

end OAI
