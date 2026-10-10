import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row0
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row1
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row2
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row3
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row4
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row5
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row6
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row7
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row8
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row9
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row10
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row11
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row12
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row13
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row14
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row15
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row16
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row17
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row18
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row19
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row20
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row21
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row22
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row23
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row24
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row25
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Row26

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

theorem entryEvalRow0 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 0 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 0).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow1 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 1 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 1).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow2 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 2 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 2).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow3 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 3).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow4 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 4).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow5 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 5 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 5).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow6 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 6 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 6).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow7 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 7 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 7).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow8 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 8 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 8).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow9 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 9 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 9).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow10 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 10 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 10).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow11 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 11 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 11).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow12 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 12 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 12).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow13 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 13 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 13).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow14 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 14 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 14).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow15 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 15 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 15).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow16 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 16 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 16).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow17 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 17 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 17).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow18 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 18 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 18).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow19 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 19 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 19).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow20 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 20 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 20).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval21_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow21 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 21 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 21).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval21_0 B hB
  · exact entryEval21_1 B hB
  · exact entryEval21_2 B hB
  · exact entryEval21_3 B hB
  · exact entryEval21_4 B hB
  · exact entryEval21_5 B hB
  · exact entryEval21_6 B hB
  · exact entryEval21_7 B hB
  · exact entryEval21_8 B hB
  · exact entryEval21_9 B hB
  · exact entryEval21_10 B hB
  · exact entryEval21_11 B hB
  · exact entryEval21_12 B hB
  · exact entryEval21_13 B hB
  · exact entryEval21_14 B hB
  · exact entryEval21_15 B hB
  · exact entryEval21_16 B hB
  · exact entryEval21_17 B hB
  · exact entryEval21_18 B hB
  · exact entryEval21_19 B hB
  · exact entryEval21_20 B hB
  · exact entryEval21_21 B hB
  · exact (entryEval22_21 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_21 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_21 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_21 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_21 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow22 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 22 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 22).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval22_0 B hB
  · exact entryEval22_1 B hB
  · exact entryEval22_2 B hB
  · exact entryEval22_3 B hB
  · exact entryEval22_4 B hB
  · exact entryEval22_5 B hB
  · exact entryEval22_6 B hB
  · exact entryEval22_7 B hB
  · exact entryEval22_8 B hB
  · exact entryEval22_9 B hB
  · exact entryEval22_10 B hB
  · exact entryEval22_11 B hB
  · exact entryEval22_12 B hB
  · exact entryEval22_13 B hB
  · exact entryEval22_14 B hB
  · exact entryEval22_15 B hB
  · exact entryEval22_16 B hB
  · exact entryEval22_17 B hB
  · exact entryEval22_18 B hB
  · exact entryEval22_19 B hB
  · exact entryEval22_20 B hB
  · exact entryEval22_21 B hB
  · exact entryEval22_22 B hB
  · exact (entryEval23_22 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_22 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_22 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_22 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow23 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 23 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 23).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval23_0 B hB
  · exact entryEval23_1 B hB
  · exact entryEval23_2 B hB
  · exact entryEval23_3 B hB
  · exact entryEval23_4 B hB
  · exact entryEval23_5 B hB
  · exact entryEval23_6 B hB
  · exact entryEval23_7 B hB
  · exact entryEval23_8 B hB
  · exact entryEval23_9 B hB
  · exact entryEval23_10 B hB
  · exact entryEval23_11 B hB
  · exact entryEval23_12 B hB
  · exact entryEval23_13 B hB
  · exact entryEval23_14 B hB
  · exact entryEval23_15 B hB
  · exact entryEval23_16 B hB
  · exact entryEval23_17 B hB
  · exact entryEval23_18 B hB
  · exact entryEval23_19 B hB
  · exact entryEval23_20 B hB
  · exact entryEval23_21 B hB
  · exact entryEval23_22 B hB
  · exact entryEval23_23 B hB
  · exact (entryEval24_23 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_23 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_23 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow24 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 24 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 24).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval24_0 B hB
  · exact entryEval24_1 B hB
  · exact entryEval24_2 B hB
  · exact entryEval24_3 B hB
  · exact entryEval24_4 B hB
  · exact entryEval24_5 B hB
  · exact entryEval24_6 B hB
  · exact entryEval24_7 B hB
  · exact entryEval24_8 B hB
  · exact entryEval24_9 B hB
  · exact entryEval24_10 B hB
  · exact entryEval24_11 B hB
  · exact entryEval24_12 B hB
  · exact entryEval24_13 B hB
  · exact entryEval24_14 B hB
  · exact entryEval24_15 B hB
  · exact entryEval24_16 B hB
  · exact entryEval24_17 B hB
  · exact entryEval24_18 B hB
  · exact entryEval24_19 B hB
  · exact entryEval24_20 B hB
  · exact entryEval24_21 B hB
  · exact entryEval24_22 B hB
  · exact entryEval24_23 B hB
  · exact entryEval24_24 B hB
  · exact (entryEval25_24 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_24 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow25 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 25 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 25).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval25_0 B hB
  · exact entryEval25_1 B hB
  · exact entryEval25_2 B hB
  · exact entryEval25_3 B hB
  · exact entryEval25_4 B hB
  · exact entryEval25_5 B hB
  · exact entryEval25_6 B hB
  · exact entryEval25_7 B hB
  · exact entryEval25_8 B hB
  · exact entryEval25_9 B hB
  · exact entryEval25_10 B hB
  · exact entryEval25_11 B hB
  · exact entryEval25_12 B hB
  · exact entryEval25_13 B hB
  · exact entryEval25_14 B hB
  · exact entryEval25_15 B hB
  · exact entryEval25_16 B hB
  · exact entryEval25_17 B hB
  · exact entryEval25_18 B hB
  · exact entryEval25_19 B hB
  · exact entryEval25_20 B hB
  · exact entryEval25_21 B hB
  · exact entryEval25_22 B hB
  · exact entryEval25_23 B hB
  · exact entryEval25_24 B hB
  · exact entryEval25_25 B hB
  · exact (entryEval26_25 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow26 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 26 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 26).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval26_0 B hB
  · exact entryEval26_1 B hB
  · exact entryEval26_2 B hB
  · exact entryEval26_3 B hB
  · exact entryEval26_4 B hB
  · exact entryEval26_5 B hB
  · exact entryEval26_6 B hB
  · exact entryEval26_7 B hB
  · exact entryEval26_8 B hB
  · exact entryEval26_9 B hB
  · exact entryEval26_10 B hB
  · exact entryEval26_11 B hB
  · exact entryEval26_12 B hB
  · exact entryEval26_13 B hB
  · exact entryEval26_14 B hB
  · exact entryEval26_15 B hB
  · exact entryEval26_16 B hB
  · exact entryEval26_17 B hB
  · exact entryEval26_18 B hB
  · exact entryEval26_19 B hB
  · exact entryEval26_20 B hB
  · exact entryEval26_21 B hB
  · exact entryEval26_22 B hB
  · exact entryEval26_23 B hB
  · exact entryEval26_24 B hB
  · exact entryEval26_25 B hB
  · exact entryEval26_26 B hB

theorem entryEval (i j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms i).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact entryEvalRow21 j B hB
  · exact entryEvalRow22 j B hB
  · exact entryEvalRow23 j B hB
  · exact entryEvalRow24 j B hB
  · exact entryEvalRow25 j B hB
  · exact entryEvalRow26 j B hB

end MUB6.Certificate.GramEntries.Block3

end OAI
