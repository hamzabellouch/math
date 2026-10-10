import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block130
import OAI.Analysis.MutuallyUnbiased.GramRows.Block131
import OAI.Analysis.MutuallyUnbiased.GramRows.Block132
import OAI.Analysis.MutuallyUnbiased.GramRows.Block142
import OAI.Analysis.MutuallyUnbiased.GramRows.Block143
import OAI.Analysis.MutuallyUnbiased.GramRows.Block144
import OAI.Analysis.MutuallyUnbiased.GramRows.Block145

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows13_0 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15177, row15178, row15179, row15180, row15181, row15182, row15183, row15184, row15185, row15186, row15187, row15188, row13593, row13594, row13595, row13596, row13597, row13598, row15189, row15190, row15191, row15192, row15193, row15194, row13602, row13603, row13604, row13605, row13606, row13607, row13608, row13609, row13610, row13611, row13612, row13613]

theorem entryCheck13_0 : entry13_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_0 k)) := by decide +kernel

theorem rowsSound13_0 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval15177 x
  · exact rowEval15178 x
  · exact rowEval15179 x
  · exact rowEval15180 x
  · exact rowEval15181 x
  · exact rowEval15182 x
  · exact rowEval15183 x
  · exact rowEval15184 x
  · exact rowEval15185 x
  · exact rowEval15186 x
  · exact rowEval15187 x
  · exact rowEval15188 x
  · exact rowEval13593 x
  · exact rowEval13594 x
  · exact rowEval13595 x
  · exact rowEval13596 x
  · exact rowEval13597 x
  · exact rowEval13598 x
  · exact rowEval15189 x
  · exact rowEval15190 x
  · exact rowEval15191 x
  · exact rowEval15192 x
  · exact rowEval15193 x
  · exact rowEval15194 x
  · exact rowEval13602 x
  · exact rowEval13603 x
  · exact rowEval13604 x
  · exact rowEval13605 x
  · exact rowEval13606 x
  · exact rowEval13607 x
  · exact rowEval13608 x
  · exact rowEval13609 x
  · exact rowEval13610 x
  · exact rowEval13611 x
  · exact rowEval13612 x
  · exact rowEval13613 x

theorem entryEval13_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_0 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck13_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_0]

def rows13_1 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15195, row15196, row15197, row15198, row15199, row15200, row15201, row15202, row15203, row15204, row15205, row15206, row13629, row13630, row13631, row13632, row13633, row13634, row15207, row15208, row15209, row15210, row15211, row15212, row13638, row13639, row13640, row13641, row13642, row13643, row13644, row13645, row13646, row13647, row13648, row13649]

theorem entryCheck13_1 : entry13_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_1 k)) := by decide +kernel

theorem rowsSound13_1 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval15195 x
  · exact rowEval15196 x
  · exact rowEval15197 x
  · exact rowEval15198 x
  · exact rowEval15199 x
  · exact rowEval15200 x
  · exact rowEval15201 x
  · exact rowEval15202 x
  · exact rowEval15203 x
  · exact rowEval15204 x
  · exact rowEval15205 x
  · exact rowEval15206 x
  · exact rowEval13629 x
  · exact rowEval13630 x
  · exact rowEval13631 x
  · exact rowEval13632 x
  · exact rowEval13633 x
  · exact rowEval13634 x
  · exact rowEval15207 x
  · exact rowEval15208 x
  · exact rowEval15209 x
  · exact rowEval15210 x
  · exact rowEval15211 x
  · exact rowEval15212 x
  · exact rowEval13638 x
  · exact rowEval13639 x
  · exact rowEval13640 x
  · exact rowEval13641 x
  · exact rowEval13642 x
  · exact rowEval13643 x
  · exact rowEval13644 x
  · exact rowEval13645 x
  · exact rowEval13646 x
  · exact rowEval13647 x
  · exact rowEval13648 x
  · exact rowEval13649 x

theorem entryEval13_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_1 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck13_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_1]

def rows13_2 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15213, row15214, row15215, row15216, row15217, row15218, row15219, row15220, row15221, row15222, row15223, row15224, row13665, row13666, row13667, row13668, row13669, row13670, row15225, row15226, row15227, row15228, row15229, row15230, row13674, row13675, row13676, row13677, row13678, row13679, row13680, row13681, row13682, row13683, row13684, row13685]

theorem entryCheck13_2 : entry13_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_2 k)) := by decide +kernel

theorem rowsSound13_2 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval15213 x
  · exact rowEval15214 x
  · exact rowEval15215 x
  · exact rowEval15216 x
  · exact rowEval15217 x
  · exact rowEval15218 x
  · exact rowEval15219 x
  · exact rowEval15220 x
  · exact rowEval15221 x
  · exact rowEval15222 x
  · exact rowEval15223 x
  · exact rowEval15224 x
  · exact rowEval13665 x
  · exact rowEval13666 x
  · exact rowEval13667 x
  · exact rowEval13668 x
  · exact rowEval13669 x
  · exact rowEval13670 x
  · exact rowEval15225 x
  · exact rowEval15226 x
  · exact rowEval15227 x
  · exact rowEval15228 x
  · exact rowEval15229 x
  · exact rowEval15230 x
  · exact rowEval13674 x
  · exact rowEval13675 x
  · exact rowEval13676 x
  · exact rowEval13677 x
  · exact rowEval13678 x
  · exact rowEval13679 x
  · exact rowEval13680 x
  · exact rowEval13681 x
  · exact rowEval13682 x
  · exact rowEval13683 x
  · exact rowEval13684 x
  · exact rowEval13685 x

theorem entryEval13_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_2 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck13_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_2]

def rows13_3 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15231, row15232, row15233, row15234, row15235, row15236, row15237, row15238, row15239, row15240, row15241, row15242, row13701, row13702, row13703, row13704, row13705, row13706, row15243, row15244, row15245, row15246, row15247, row15248, row13710, row13711, row13712, row13713, row13714, row13715, row13716, row13717, row13718, row13719, row13720, row13721]

theorem entryCheck13_3 : entry13_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_3 k)) := by decide +kernel

theorem rowsSound13_3 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval15231 x
  · exact rowEval15232 x
  · exact rowEval15233 x
  · exact rowEval15234 x
  · exact rowEval15235 x
  · exact rowEval15236 x
  · exact rowEval15237 x
  · exact rowEval15238 x
  · exact rowEval15239 x
  · exact rowEval15240 x
  · exact rowEval15241 x
  · exact rowEval15242 x
  · exact rowEval13701 x
  · exact rowEval13702 x
  · exact rowEval13703 x
  · exact rowEval13704 x
  · exact rowEval13705 x
  · exact rowEval13706 x
  · exact rowEval15243 x
  · exact rowEval15244 x
  · exact rowEval15245 x
  · exact rowEval15246 x
  · exact rowEval15247 x
  · exact rowEval15248 x
  · exact rowEval13710 x
  · exact rowEval13711 x
  · exact rowEval13712 x
  · exact rowEval13713 x
  · exact rowEval13714 x
  · exact rowEval13715 x
  · exact rowEval13716 x
  · exact rowEval13717 x
  · exact rowEval13718 x
  · exact rowEval13719 x
  · exact rowEval13720 x
  · exact rowEval13721 x

theorem entryEval13_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_3 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck13_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_3]

def rows13_4 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15249, row15250, row15251, row15252, row15253, row15254, row15255, row15256, row15257, row15258, row15259, row15260, row13737, row13738, row13739, row13740, row13741, row13742, row15261, row15262, row15263, row15264, row15265, row15266, row13746, row13747, row13748, row13749, row13750, row13751, row13752, row13753, row13754, row13755, row13756, row13757]

theorem entryCheck13_4 : entry13_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_4 k)) := by decide +kernel

theorem rowsSound13_4 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval15249 x
  · exact rowEval15250 x
  · exact rowEval15251 x
  · exact rowEval15252 x
  · exact rowEval15253 x
  · exact rowEval15254 x
  · exact rowEval15255 x
  · exact rowEval15256 x
  · exact rowEval15257 x
  · exact rowEval15258 x
  · exact rowEval15259 x
  · exact rowEval15260 x
  · exact rowEval13737 x
  · exact rowEval13738 x
  · exact rowEval13739 x
  · exact rowEval13740 x
  · exact rowEval13741 x
  · exact rowEval13742 x
  · exact rowEval15261 x
  · exact rowEval15262 x
  · exact rowEval15263 x
  · exact rowEval15264 x
  · exact rowEval15265 x
  · exact rowEval15266 x
  · exact rowEval13746 x
  · exact rowEval13747 x
  · exact rowEval13748 x
  · exact rowEval13749 x
  · exact rowEval13750 x
  · exact rowEval13751 x
  · exact rowEval13752 x
  · exact rowEval13753 x
  · exact rowEval13754 x
  · exact rowEval13755 x
  · exact rowEval13756 x
  · exact rowEval13757 x

theorem entryEval13_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_4 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck13_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_4]

def rows13_5 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15267, row15268, row15269, row15270, row15271, row15272, row15273, row15274, row15275, row15276, row15277, row15278, row13773, row13774, row13775, row13776, row13777, row13778, row15279, row15280, row15281, row15282, row15283, row15284, row13782, row13783, row13784, row13785, row13786, row13787, row13788, row13789, row13790, row13791, row13792, row13793]

theorem entryCheck13_5 : entry13_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_5 k)) := by decide +kernel

theorem rowsSound13_5 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval15267 x
  · exact rowEval15268 x
  · exact rowEval15269 x
  · exact rowEval15270 x
  · exact rowEval15271 x
  · exact rowEval15272 x
  · exact rowEval15273 x
  · exact rowEval15274 x
  · exact rowEval15275 x
  · exact rowEval15276 x
  · exact rowEval15277 x
  · exact rowEval15278 x
  · exact rowEval13773 x
  · exact rowEval13774 x
  · exact rowEval13775 x
  · exact rowEval13776 x
  · exact rowEval13777 x
  · exact rowEval13778 x
  · exact rowEval15279 x
  · exact rowEval15280 x
  · exact rowEval15281 x
  · exact rowEval15282 x
  · exact rowEval15283 x
  · exact rowEval15284 x
  · exact rowEval13782 x
  · exact rowEval13783 x
  · exact rowEval13784 x
  · exact rowEval13785 x
  · exact rowEval13786 x
  · exact rowEval13787 x
  · exact rowEval13788 x
  · exact rowEval13789 x
  · exact rowEval13790 x
  · exact rowEval13791 x
  · exact rowEval13792 x
  · exact rowEval13793 x

theorem entryEval13_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_5 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck13_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_5]

def rows13_6 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15285, row15286, row15287, row15288, row15289, row15290, row15291, row15292, row15293, row15294, row15295, row15296, row13809, row13810, row13811, row13812, row13813, row13814, row15297, row15298, row15299, row15300, row15301, row15302, row13818, row13819, row13820, row13821, row13822, row13823, row13824, row13825, row13826, row13827, row13828, row13829]

theorem entryCheck13_6 : entry13_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_6 k)) := by decide +kernel

theorem rowsSound13_6 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval15285 x
  · exact rowEval15286 x
  · exact rowEval15287 x
  · exact rowEval15288 x
  · exact rowEval15289 x
  · exact rowEval15290 x
  · exact rowEval15291 x
  · exact rowEval15292 x
  · exact rowEval15293 x
  · exact rowEval15294 x
  · exact rowEval15295 x
  · exact rowEval15296 x
  · exact rowEval13809 x
  · exact rowEval13810 x
  · exact rowEval13811 x
  · exact rowEval13812 x
  · exact rowEval13813 x
  · exact rowEval13814 x
  · exact rowEval15297 x
  · exact rowEval15298 x
  · exact rowEval15299 x
  · exact rowEval15300 x
  · exact rowEval15301 x
  · exact rowEval15302 x
  · exact rowEval13818 x
  · exact rowEval13819 x
  · exact rowEval13820 x
  · exact rowEval13821 x
  · exact rowEval13822 x
  · exact rowEval13823 x
  · exact rowEval13824 x
  · exact rowEval13825 x
  · exact rowEval13826 x
  · exact rowEval13827 x
  · exact rowEval13828 x
  · exact rowEval13829 x

theorem entryEval13_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_6 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck13_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_6]

def rows13_7 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15303, row15304, row15305, row15306, row15307, row15308, row15309, row15310, row15311, row15312, row15313, row15314, row15315, row15316, row15317, row15318, row15319, row15320, row15321, row15322, row15323, row15324, row15325, row15326, row15327, row15328, row15329, row15330, row15331, row15332, row15333, row15334, row15335, row15336, row15337, row15338]

theorem entryCheck13_7 : entry13_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_7 k)) := by decide +kernel

theorem rowsSound13_7 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval15303 x
  · exact rowEval15304 x
  · exact rowEval15305 x
  · exact rowEval15306 x
  · exact rowEval15307 x
  · exact rowEval15308 x
  · exact rowEval15309 x
  · exact rowEval15310 x
  · exact rowEval15311 x
  · exact rowEval15312 x
  · exact rowEval15313 x
  · exact rowEval15314 x
  · exact rowEval15315 x
  · exact rowEval15316 x
  · exact rowEval15317 x
  · exact rowEval15318 x
  · exact rowEval15319 x
  · exact rowEval15320 x
  · exact rowEval15321 x
  · exact rowEval15322 x
  · exact rowEval15323 x
  · exact rowEval15324 x
  · exact rowEval15325 x
  · exact rowEval15326 x
  · exact rowEval15327 x
  · exact rowEval15328 x
  · exact rowEval15329 x
  · exact rowEval15330 x
  · exact rowEval15331 x
  · exact rowEval15332 x
  · exact rowEval15333 x
  · exact rowEval15334 x
  · exact rowEval15335 x
  · exact rowEval15336 x
  · exact rowEval15337 x
  · exact rowEval15338 x

theorem entryEval13_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_7 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck13_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_7]

def rows13_8 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15339, row15340, row15341, row15342, row15343, row15344, row15345, row15346, row15347, row15348, row15349, row15350, row15351, row15352, row15353, row15354, row15355, row15356, row15357, row15358, row15359, row15360, row15361, row15362, row15363, row15364, row15365, row15366, row15367, row15368, row15369, row15370, row15371, row15372, row15373, row15374]

theorem entryCheck13_8 : entry13_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_8 k)) := by decide +kernel

theorem rowsSound13_8 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval15339 x
  · exact rowEval15340 x
  · exact rowEval15341 x
  · exact rowEval15342 x
  · exact rowEval15343 x
  · exact rowEval15344 x
  · exact rowEval15345 x
  · exact rowEval15346 x
  · exact rowEval15347 x
  · exact rowEval15348 x
  · exact rowEval15349 x
  · exact rowEval15350 x
  · exact rowEval15351 x
  · exact rowEval15352 x
  · exact rowEval15353 x
  · exact rowEval15354 x
  · exact rowEval15355 x
  · exact rowEval15356 x
  · exact rowEval15357 x
  · exact rowEval15358 x
  · exact rowEval15359 x
  · exact rowEval15360 x
  · exact rowEval15361 x
  · exact rowEval15362 x
  · exact rowEval15363 x
  · exact rowEval15364 x
  · exact rowEval15365 x
  · exact rowEval15366 x
  · exact rowEval15367 x
  · exact rowEval15368 x
  · exact rowEval15369 x
  · exact rowEval15370 x
  · exact rowEval15371 x
  · exact rowEval15372 x
  · exact rowEval15373 x
  · exact rowEval15374 x

theorem entryEval13_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_8 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck13_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_8]

def rows13_9 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15375, row15376, row15377, row15378, row15379, row15380, row15381, row15382, row15383, row15384, row15385, row15386, row15387, row15388, row15389, row15390, row15391, row15392, row15393, row15394, row15395, row15396, row15397, row15398, row15399, row15400, row15401, row15402, row15403, row15404, row15405, row15406, row15407, row15408, row15409, row15410]

theorem entryCheck13_9 : entry13_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_9 k)) := by decide +kernel

theorem rowsSound13_9 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval15375 x
  · exact rowEval15376 x
  · exact rowEval15377 x
  · exact rowEval15378 x
  · exact rowEval15379 x
  · exact rowEval15380 x
  · exact rowEval15381 x
  · exact rowEval15382 x
  · exact rowEval15383 x
  · exact rowEval15384 x
  · exact rowEval15385 x
  · exact rowEval15386 x
  · exact rowEval15387 x
  · exact rowEval15388 x
  · exact rowEval15389 x
  · exact rowEval15390 x
  · exact rowEval15391 x
  · exact rowEval15392 x
  · exact rowEval15393 x
  · exact rowEval15394 x
  · exact rowEval15395 x
  · exact rowEval15396 x
  · exact rowEval15397 x
  · exact rowEval15398 x
  · exact rowEval15399 x
  · exact rowEval15400 x
  · exact rowEval15401 x
  · exact rowEval15402 x
  · exact rowEval15403 x
  · exact rowEval15404 x
  · exact rowEval15405 x
  · exact rowEval15406 x
  · exact rowEval15407 x
  · exact rowEval15408 x
  · exact rowEval15409 x
  · exact rowEval15410 x

theorem entryEval13_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_9 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck13_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_9]

def rows13_10 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15411, row15412, row15413, row15414, row15415, row15416, row15417, row15418, row15419, row15420, row15421, row15422, row15423, row15424, row15425, row15426, row15427, row15428, row15429, row15430, row15431, row15432, row15433, row15434, row15435, row15436, row15437, row15438, row15439, row15440, row15441, row15442, row15443, row15444, row15445, row15446]

theorem entryCheck13_10 : entry13_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_10 k)) := by decide +kernel

theorem rowsSound13_10 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval15411 x
  · exact rowEval15412 x
  · exact rowEval15413 x
  · exact rowEval15414 x
  · exact rowEval15415 x
  · exact rowEval15416 x
  · exact rowEval15417 x
  · exact rowEval15418 x
  · exact rowEval15419 x
  · exact rowEval15420 x
  · exact rowEval15421 x
  · exact rowEval15422 x
  · exact rowEval15423 x
  · exact rowEval15424 x
  · exact rowEval15425 x
  · exact rowEval15426 x
  · exact rowEval15427 x
  · exact rowEval15428 x
  · exact rowEval15429 x
  · exact rowEval15430 x
  · exact rowEval15431 x
  · exact rowEval15432 x
  · exact rowEval15433 x
  · exact rowEval15434 x
  · exact rowEval15435 x
  · exact rowEval15436 x
  · exact rowEval15437 x
  · exact rowEval15438 x
  · exact rowEval15439 x
  · exact rowEval15440 x
  · exact rowEval15441 x
  · exact rowEval15442 x
  · exact rowEval15443 x
  · exact rowEval15444 x
  · exact rowEval15445 x
  · exact rowEval15446 x

theorem entryEval13_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_10 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck13_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_10]

def rows13_11 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15447, row15448, row15449, row15450, row15451, row15452, row15453, row15454, row15455, row15456, row15457, row15458, row15459, row15460, row15461, row15462, row15463, row15464, row15465, row15466, row15467, row15468, row15469, row15470, row15471, row15472, row15473, row15474, row15475, row15476, row15477, row15478, row15479, row15480, row15481, row15482]

theorem entryCheck13_11 : entry13_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_11 k)) := by decide +kernel

theorem rowsSound13_11 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval15447 x
  · exact rowEval15448 x
  · exact rowEval15449 x
  · exact rowEval15450 x
  · exact rowEval15451 x
  · exact rowEval15452 x
  · exact rowEval15453 x
  · exact rowEval15454 x
  · exact rowEval15455 x
  · exact rowEval15456 x
  · exact rowEval15457 x
  · exact rowEval15458 x
  · exact rowEval15459 x
  · exact rowEval15460 x
  · exact rowEval15461 x
  · exact rowEval15462 x
  · exact rowEval15463 x
  · exact rowEval15464 x
  · exact rowEval15465 x
  · exact rowEval15466 x
  · exact rowEval15467 x
  · exact rowEval15468 x
  · exact rowEval15469 x
  · exact rowEval15470 x
  · exact rowEval15471 x
  · exact rowEval15472 x
  · exact rowEval15473 x
  · exact rowEval15474 x
  · exact rowEval15475 x
  · exact rowEval15476 x
  · exact rowEval15477 x
  · exact rowEval15478 x
  · exact rowEval15479 x
  · exact rowEval15480 x
  · exact rowEval15481 x
  · exact rowEval15482 x

theorem entryEval13_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_11 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck13_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_11]

def rows13_12 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15483, row15484, row15485, row15486, row15487, row15488, row15489, row15490, row15491, row15492, row15493, row15494, row15495, row15496, row15497, row15498, row15499, row15500, row15501, row15502, row15503, row15504, row15505, row15506, row15507, row15508, row15509, row15510, row15511, row15512, row15513, row15514, row15515, row15516, row15517, row15518]

theorem entryCheck13_12 : entry13_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_12 k)) := by decide +kernel

theorem rowsSound13_12 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval15483 x
  · exact rowEval15484 x
  · exact rowEval15485 x
  · exact rowEval15486 x
  · exact rowEval15487 x
  · exact rowEval15488 x
  · exact rowEval15489 x
  · exact rowEval15490 x
  · exact rowEval15491 x
  · exact rowEval15492 x
  · exact rowEval15493 x
  · exact rowEval15494 x
  · exact rowEval15495 x
  · exact rowEval15496 x
  · exact rowEval15497 x
  · exact rowEval15498 x
  · exact rowEval15499 x
  · exact rowEval15500 x
  · exact rowEval15501 x
  · exact rowEval15502 x
  · exact rowEval15503 x
  · exact rowEval15504 x
  · exact rowEval15505 x
  · exact rowEval15506 x
  · exact rowEval15507 x
  · exact rowEval15508 x
  · exact rowEval15509 x
  · exact rowEval15510 x
  · exact rowEval15511 x
  · exact rowEval15512 x
  · exact rowEval15513 x
  · exact rowEval15514 x
  · exact rowEval15515 x
  · exact rowEval15516 x
  · exact rowEval15517 x
  · exact rowEval15518 x

theorem entryEval13_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_12 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck13_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_12]

def rows13_13 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15519, row15520, row15521, row15522, row15523, row15524, row15525, row15526, row15527, row15528, row15529, row15530, row15531, row15532, row15533, row15534, row15535, row15536, row15537, row15538, row15539, row15540, row15541, row15542, row15543, row15544, row15545, row15546, row15547, row15548, row15549, row15550, row15551, row15552, row15553, row15554]

theorem entryCheck13_13 : entry13_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_13 k)) := by decide +kernel

theorem rowsSound13_13 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval15519 x
  · exact rowEval15520 x
  · exact rowEval15521 x
  · exact rowEval15522 x
  · exact rowEval15523 x
  · exact rowEval15524 x
  · exact rowEval15525 x
  · exact rowEval15526 x
  · exact rowEval15527 x
  · exact rowEval15528 x
  · exact rowEval15529 x
  · exact rowEval15530 x
  · exact rowEval15531 x
  · exact rowEval15532 x
  · exact rowEval15533 x
  · exact rowEval15534 x
  · exact rowEval15535 x
  · exact rowEval15536 x
  · exact rowEval15537 x
  · exact rowEval15538 x
  · exact rowEval15539 x
  · exact rowEval15540 x
  · exact rowEval15541 x
  · exact rowEval15542 x
  · exact rowEval15543 x
  · exact rowEval15544 x
  · exact rowEval15545 x
  · exact rowEval15546 x
  · exact rowEval15547 x
  · exact rowEval15548 x
  · exact rowEval15549 x
  · exact rowEval15550 x
  · exact rowEval15551 x
  · exact rowEval15552 x
  · exact rowEval15553 x
  · exact rowEval15554 x

theorem entryEval13_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_13 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck13_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_13]

end MUB6.Certificate.GramEntries.Block4

end OAI
