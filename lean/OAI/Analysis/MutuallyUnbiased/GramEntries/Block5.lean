import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row0
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row1
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row2
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row3
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row4
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row5
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row6
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row7
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row8
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row9
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row10
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Row11

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

theorem entryEvalRow0 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 0 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 0).mixedGram (GramFunctions.Block5.forms j) B := by
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
  · exact (entryEval5_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow1 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 1 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 1).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval1_0 B hB
  · exact entryEval1_1 B hB
  · exact (entryEval2_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow2 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 2 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 2).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval2_0 B hB
  · exact entryEval2_1 B hB
  · exact entryEval2_2 B hB
  · exact (entryEval3_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow3 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 3).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval3_0 B hB
  · exact entryEval3_1 B hB
  · exact entryEval3_2 B hB
  · exact entryEval3_3 B hB
  · exact (entryEval4_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow4 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 4).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval4_0 B hB
  · exact entryEval4_1 B hB
  · exact entryEval4_2 B hB
  · exact entryEval4_3 B hB
  · exact entryEval4_4 B hB
  · exact (entryEval5_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow5 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 5 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 5).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval5_0 B hB
  · exact entryEval5_1 B hB
  · exact entryEval5_2 B hB
  · exact entryEval5_3 B hB
  · exact entryEval5_4 B hB
  · exact entryEval5_5 B hB
  · exact (entryEval6_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow6 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 6 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 6).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval6_0 B hB
  · exact entryEval6_1 B hB
  · exact entryEval6_2 B hB
  · exact entryEval6_3 B hB
  · exact entryEval6_4 B hB
  · exact entryEval6_5 B hB
  · exact entryEval6_6 B hB
  · exact (entryEval7_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow7 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 7 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 7).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval7_0 B hB
  · exact entryEval7_1 B hB
  · exact entryEval7_2 B hB
  · exact entryEval7_3 B hB
  · exact entryEval7_4 B hB
  · exact entryEval7_5 B hB
  · exact entryEval7_6 B hB
  · exact entryEval7_7 B hB
  · exact (entryEval8_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow8 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 8 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 8).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval8_0 B hB
  · exact entryEval8_1 B hB
  · exact entryEval8_2 B hB
  · exact entryEval8_3 B hB
  · exact entryEval8_4 B hB
  · exact entryEval8_5 B hB
  · exact entryEval8_6 B hB
  · exact entryEval8_7 B hB
  · exact entryEval8_8 B hB
  · exact (entryEval9_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow9 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 9 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 9).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval9_0 B hB
  · exact entryEval9_1 B hB
  · exact entryEval9_2 B hB
  · exact entryEval9_3 B hB
  · exact entryEval9_4 B hB
  · exact entryEval9_5 B hB
  · exact entryEval9_6 B hB
  · exact entryEval9_7 B hB
  · exact entryEval9_8 B hB
  · exact entryEval9_9 B hB
  · exact (entryEval10_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow10 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 10 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 10).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval10_0 B hB
  · exact entryEval10_1 B hB
  · exact entryEval10_2 B hB
  · exact entryEval10_3 B hB
  · exact entryEval10_4 B hB
  · exact entryEval10_5 B hB
  · exact entryEval10_6 B hB
  · exact entryEval10_7 B hB
  · exact entryEval10_8 B hB
  · exact entryEval10_9 B hB
  · exact entryEval10_10 B hB
  · exact (entryEval11_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow11 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 11 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 11).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval11_0 B hB
  · exact entryEval11_1 B hB
  · exact entryEval11_2 B hB
  · exact entryEval11_3 B hB
  · exact entryEval11_4 B hB
  · exact entryEval11_5 B hB
  · exact entryEval11_6 B hB
  · exact entryEval11_7 B hB
  · exact entryEval11_8 B hB
  · exact entryEval11_9 B hB
  · exact entryEval11_10 B hB
  · exact entryEval11_11 B hB

theorem entryEval (i j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms i).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases i
  · exact entryEvalRow0 j B hB
  · exact entryEvalRow1 j B hB
  · exact entryEvalRow2 j B hB
  · exact entryEvalRow3 j B hB
  · exact entryEvalRow4 j B hB
  · exact entryEvalRow5 j B hB
  · exact entryEvalRow6 j B hB
  · exact entryEvalRow7 j B hB
  · exact entryEvalRow8 j B hB
  · exact entryEvalRow9 j B hB
  · exact entryEvalRow10 j B hB
  · exact entryEvalRow11 j B hB

end MUB6.Certificate.GramEntries.Block5

end OAI
