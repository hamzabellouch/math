import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row0
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row1
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row2
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row3
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row4
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row5
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row6
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row7
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row8
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row9
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row10
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row11
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row12
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row13
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row14
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row15
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row16
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row17
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row18
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row19
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Row20

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

theorem entryEvalRow0 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 0 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 0).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow1 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 1 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 1).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow2 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 2 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 2).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow3 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 3).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow4 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 4).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow5 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 5 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 5).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow6 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 6 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 6).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow7 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 7 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 7).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow8 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 8 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 8).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow9 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 9 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 9).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow10 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 10 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 10).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow11 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 11 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 11).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact (entryEval12_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow12 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 12 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 12).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval12_0 B hB
  · exact entryEval12_1 B hB
  · exact entryEval12_2 B hB
  · exact entryEval12_3 B hB
  · exact entryEval12_4 B hB
  · exact entryEval12_5 B hB
  · exact entryEval12_6 B hB
  · exact entryEval12_7 B hB
  · exact entryEval12_8 B hB
  · exact entryEval12_9 B hB
  · exact entryEval12_10 B hB
  · exact entryEval12_11 B hB
  · exact entryEval12_12 B hB
  · exact (entryEval13_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow13 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 13 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 13).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval13_0 B hB
  · exact entryEval13_1 B hB
  · exact entryEval13_2 B hB
  · exact entryEval13_3 B hB
  · exact entryEval13_4 B hB
  · exact entryEval13_5 B hB
  · exact entryEval13_6 B hB
  · exact entryEval13_7 B hB
  · exact entryEval13_8 B hB
  · exact entryEval13_9 B hB
  · exact entryEval13_10 B hB
  · exact entryEval13_11 B hB
  · exact entryEval13_12 B hB
  · exact entryEval13_13 B hB
  · exact (entryEval14_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow14 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 14 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 14).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval14_0 B hB
  · exact entryEval14_1 B hB
  · exact entryEval14_2 B hB
  · exact entryEval14_3 B hB
  · exact entryEval14_4 B hB
  · exact entryEval14_5 B hB
  · exact entryEval14_6 B hB
  · exact entryEval14_7 B hB
  · exact entryEval14_8 B hB
  · exact entryEval14_9 B hB
  · exact entryEval14_10 B hB
  · exact entryEval14_11 B hB
  · exact entryEval14_12 B hB
  · exact entryEval14_13 B hB
  · exact entryEval14_14 B hB
  · exact (entryEval15_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow15 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 15 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 15).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval15_0 B hB
  · exact entryEval15_1 B hB
  · exact entryEval15_2 B hB
  · exact entryEval15_3 B hB
  · exact entryEval15_4 B hB
  · exact entryEval15_5 B hB
  · exact entryEval15_6 B hB
  · exact entryEval15_7 B hB
  · exact entryEval15_8 B hB
  · exact entryEval15_9 B hB
  · exact entryEval15_10 B hB
  · exact entryEval15_11 B hB
  · exact entryEval15_12 B hB
  · exact entryEval15_13 B hB
  · exact entryEval15_14 B hB
  · exact entryEval15_15 B hB
  · exact (entryEval16_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow16 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 16 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 16).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval16_0 B hB
  · exact entryEval16_1 B hB
  · exact entryEval16_2 B hB
  · exact entryEval16_3 B hB
  · exact entryEval16_4 B hB
  · exact entryEval16_5 B hB
  · exact entryEval16_6 B hB
  · exact entryEval16_7 B hB
  · exact entryEval16_8 B hB
  · exact entryEval16_9 B hB
  · exact entryEval16_10 B hB
  · exact entryEval16_11 B hB
  · exact entryEval16_12 B hB
  · exact entryEval16_13 B hB
  · exact entryEval16_14 B hB
  · exact entryEval16_15 B hB
  · exact entryEval16_16 B hB
  · exact (entryEval17_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow17 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 17 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 17).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval17_0 B hB
  · exact entryEval17_1 B hB
  · exact entryEval17_2 B hB
  · exact entryEval17_3 B hB
  · exact entryEval17_4 B hB
  · exact entryEval17_5 B hB
  · exact entryEval17_6 B hB
  · exact entryEval17_7 B hB
  · exact entryEval17_8 B hB
  · exact entryEval17_9 B hB
  · exact entryEval17_10 B hB
  · exact entryEval17_11 B hB
  · exact entryEval17_12 B hB
  · exact entryEval17_13 B hB
  · exact entryEval17_14 B hB
  · exact entryEval17_15 B hB
  · exact entryEval17_16 B hB
  · exact entryEval17_17 B hB
  · exact (entryEval18_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow18 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 18 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 18).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval18_0 B hB
  · exact entryEval18_1 B hB
  · exact entryEval18_2 B hB
  · exact entryEval18_3 B hB
  · exact entryEval18_4 B hB
  · exact entryEval18_5 B hB
  · exact entryEval18_6 B hB
  · exact entryEval18_7 B hB
  · exact entryEval18_8 B hB
  · exact entryEval18_9 B hB
  · exact entryEval18_10 B hB
  · exact entryEval18_11 B hB
  · exact entryEval18_12 B hB
  · exact entryEval18_13 B hB
  · exact entryEval18_14 B hB
  · exact entryEval18_15 B hB
  · exact entryEval18_16 B hB
  · exact entryEval18_17 B hB
  · exact entryEval18_18 B hB
  · exact (entryEval19_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow19 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 19 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 19).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval19_0 B hB
  · exact entryEval19_1 B hB
  · exact entryEval19_2 B hB
  · exact entryEval19_3 B hB
  · exact entryEval19_4 B hB
  · exact entryEval19_5 B hB
  · exact entryEval19_6 B hB
  · exact entryEval19_7 B hB
  · exact entryEval19_8 B hB
  · exact entryEval19_9 B hB
  · exact entryEval19_10 B hB
  · exact entryEval19_11 B hB
  · exact entryEval19_12 B hB
  · exact entryEval19_13 B hB
  · exact entryEval19_14 B hB
  · exact entryEval19_15 B hB
  · exact entryEval19_16 B hB
  · exact entryEval19_17 B hB
  · exact entryEval19_18 B hB
  · exact entryEval19_19 B hB
  · exact (entryEval20_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow20 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 20 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 20).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval20_0 B hB
  · exact entryEval20_1 B hB
  · exact entryEval20_2 B hB
  · exact entryEval20_3 B hB
  · exact entryEval20_4 B hB
  · exact entryEval20_5 B hB
  · exact entryEval20_6 B hB
  · exact entryEval20_7 B hB
  · exact entryEval20_8 B hB
  · exact entryEval20_9 B hB
  · exact entryEval20_10 B hB
  · exact entryEval20_11 B hB
  · exact entryEval20_12 B hB
  · exact entryEval20_13 B hB
  · exact entryEval20_14 B hB
  · exact entryEval20_15 B hB
  · exact entryEval20_16 B hB
  · exact entryEval20_17 B hB
  · exact entryEval20_18 B hB
  · exact entryEval20_19 B hB
  · exact entryEval20_20 B hB

theorem entryEval (i j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms i).mixedGram (GramFunctions.Block1.forms j) B := by
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
  · exact entryEvalRow12 j B hB
  · exact entryEvalRow13 j B hB
  · exact entryEvalRow14 j B hB
  · exact entryEvalRow15 j B hB
  · exact entryEvalRow16 j B hB
  · exact entryEvalRow17 j B hB
  · exact entryEvalRow18 j B hB
  · exact entryEvalRow19 j B hB
  · exact entryEvalRow20 j B hB

end MUB6.Certificate.GramEntries.Block1

end OAI
