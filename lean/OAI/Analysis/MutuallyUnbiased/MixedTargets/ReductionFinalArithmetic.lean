import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData59
import OAI.Analysis.MutuallyUnbiased.MixedTargets.OriginalCollection
import OAI.Analysis.MutuallyUnbiased.MixedData.Expression

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def numericRawPolynomial : Integer.Sparse (Fin 3237) := ((((MixedData.targetRow0 ++ MixedData.targetRow1) ++ (MixedData.targetRow2 ++ (MixedData.targetRow3 ++ MixedData.targetRow4))) ++ ((MixedData.targetRow5 ++ (MixedData.targetRow6 ++ MixedData.targetRow7)) ++ (MixedData.targetRow8 ++ (MixedData.targetRow9 ++ MixedData.targetRow10)))) ++ (((MixedData.targetRow11 ++ (MixedData.targetRow12 ++ MixedData.targetRow13)) ++ (MixedData.targetRow14 ++ (MixedData.targetRow15 ++ MixedData.targetRow16))) ++ ((MixedData.targetRow17 ++ (MixedData.targetRow18 ++ MixedData.targetRow19)) ++ (MixedData.targetRow20 ++ (MixedData.targetRow21 ++ MixedData.targetRow22)))))

theorem numericRawPolynomialEval (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval numericRawPolynomial x =
      Integer.Combination.eval MixedData.targetRows x MixedData.rawCombination := by
  simp only [numericRawPolynomial, Integer.Sparse.eval_append, MixedData.rawCombination, Integer.Combination.eval]
  rfl

theorem originalReductionCheck : originalMerge1917 = originalPolynomial := by decide +kernel

theorem numericReductionCheck : reducedMerge1917 =
    Integer.Sparse.collectBalanced masterLess (Integer.Sparse.reindex keyMap numericRawPolynomial) := by decide +kernel

theorem numericReductionEval (B : Fin 7 → Basis) :
    Integer.Sparse.eval reducedMerge1917 (mixedVector B) =
      Integer.Combination.eval MixedData.targetRows (numericVector B) MixedData.rawCombination := by
  rw [numericReductionCheck, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_reindex]
  exact numericRawPolynomialEval _

end MUB6.Certificate.MixedTargetSemantics

end OAI
