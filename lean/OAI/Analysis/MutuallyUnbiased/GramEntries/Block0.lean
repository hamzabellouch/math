import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Row0
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Row1
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Row2
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Row3
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Row4

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

theorem entryEvalRow0 (j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 0 j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms 0).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases j
  · exact entryEval0_0 B hB
  · exact (entryEval1_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval2_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow1 (j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 1 j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms 1).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases j
  · exact entryEval1_0 B hB
  · exact entryEval1_1 B hB
  · exact (entryEval2_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow2 (j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 2 j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms 2).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases j
  · exact entryEval2_0 B hB
  · exact entryEval2_1 B hB
  · exact entryEval2_2 B hB
  · exact (entryEval3_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow3 (j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms 3).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases j
  · exact entryEval3_0 B hB
  · exact entryEval3_1 B hB
  · exact entryEval3_2 B hB
  · exact entryEval3_3 B hB
  · exact (entryEval4_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow4 (j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms 4).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases j
  · exact entryEval4_0 B hB
  · exact entryEval4_1 B hB
  · exact entryEval4_2 B hB
  · exact entryEval4_3 B hB
  · exact entryEval4_4 B hB

theorem entryEval (i j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms i).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases i
  · exact entryEvalRow0 j B hB
  · exact entryEvalRow1 j B hB
  · exact entryEvalRow2 j B hB
  · exact entryEvalRow3 j B hB
  · exact entryEvalRow4 j B hB

end MUB6.Certificate.GramEntries.Block0

end OAI
