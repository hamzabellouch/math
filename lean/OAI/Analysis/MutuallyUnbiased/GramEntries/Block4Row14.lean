import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block130
import OAI.Analysis.MutuallyUnbiased.GramRows.Block131
import OAI.Analysis.MutuallyUnbiased.GramRows.Block132
import OAI.Analysis.MutuallyUnbiased.GramRows.Block142
import OAI.Analysis.MutuallyUnbiased.GramRows.Block143
import OAI.Analysis.MutuallyUnbiased.GramRows.Block144
import OAI.Analysis.MutuallyUnbiased.GramRows.Block145
import OAI.Analysis.MutuallyUnbiased.GramRows.Block146

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_0 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15180, row15181, row15182, row15183, row15184, row15185, row15555, row15556, row15557, row13593, row13594, row13595, row13596, row13597, row13598, row13599, row13600, row13601, row15189, row15190, row15191, row15192, row15193, row15194, row13602, row13603, row13604, row13605, row13606, row13607, row15558, row15559, row15560, row13620, row13621, row13622]

theorem entryCheck14_0 : entry14_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_0 k)) := by decide +kernel

theorem rowsSound14_0 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval15180 x
  · exact rowEval15181 x
  · exact rowEval15182 x
  · exact rowEval15183 x
  · exact rowEval15184 x
  · exact rowEval15185 x
  · exact rowEval15555 x
  · exact rowEval15556 x
  · exact rowEval15557 x
  · exact rowEval13593 x
  · exact rowEval13594 x
  · exact rowEval13595 x
  · exact rowEval13596 x
  · exact rowEval13597 x
  · exact rowEval13598 x
  · exact rowEval13599 x
  · exact rowEval13600 x
  · exact rowEval13601 x
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
  · exact rowEval15558 x
  · exact rowEval15559 x
  · exact rowEval15560 x
  · exact rowEval13620 x
  · exact rowEval13621 x
  · exact rowEval13622 x

theorem entryEval14_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_0 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck14_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_0]

def rows14_1 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15198, row15199, row15200, row15201, row15202, row15203, row15561, row15562, row15563, row13629, row13630, row13631, row13632, row13633, row13634, row13635, row13636, row13637, row15207, row15208, row15209, row15210, row15211, row15212, row13638, row13639, row13640, row13641, row13642, row13643, row15564, row15565, row15566, row13656, row13657, row13658]

theorem entryCheck14_1 : entry14_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_1 k)) := by decide +kernel

theorem rowsSound14_1 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval15198 x
  · exact rowEval15199 x
  · exact rowEval15200 x
  · exact rowEval15201 x
  · exact rowEval15202 x
  · exact rowEval15203 x
  · exact rowEval15561 x
  · exact rowEval15562 x
  · exact rowEval15563 x
  · exact rowEval13629 x
  · exact rowEval13630 x
  · exact rowEval13631 x
  · exact rowEval13632 x
  · exact rowEval13633 x
  · exact rowEval13634 x
  · exact rowEval13635 x
  · exact rowEval13636 x
  · exact rowEval13637 x
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
  · exact rowEval15564 x
  · exact rowEval15565 x
  · exact rowEval15566 x
  · exact rowEval13656 x
  · exact rowEval13657 x
  · exact rowEval13658 x

theorem entryEval14_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_1 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck14_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_1]

def rows14_2 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15216, row15217, row15218, row15219, row15220, row15221, row15567, row15568, row15569, row13665, row13666, row13667, row13668, row13669, row13670, row13671, row13672, row13673, row15225, row15226, row15227, row15228, row15229, row15230, row13674, row13675, row13676, row13677, row13678, row13679, row15570, row15571, row15572, row13692, row13693, row13694]

theorem entryCheck14_2 : entry14_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_2 k)) := by decide +kernel

theorem rowsSound14_2 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval15216 x
  · exact rowEval15217 x
  · exact rowEval15218 x
  · exact rowEval15219 x
  · exact rowEval15220 x
  · exact rowEval15221 x
  · exact rowEval15567 x
  · exact rowEval15568 x
  · exact rowEval15569 x
  · exact rowEval13665 x
  · exact rowEval13666 x
  · exact rowEval13667 x
  · exact rowEval13668 x
  · exact rowEval13669 x
  · exact rowEval13670 x
  · exact rowEval13671 x
  · exact rowEval13672 x
  · exact rowEval13673 x
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
  · exact rowEval15570 x
  · exact rowEval15571 x
  · exact rowEval15572 x
  · exact rowEval13692 x
  · exact rowEval13693 x
  · exact rowEval13694 x

theorem entryEval14_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_2 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck14_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_2]

def rows14_3 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15234, row15235, row15236, row15237, row15238, row15239, row15573, row15574, row15575, row13701, row13702, row13703, row13704, row13705, row13706, row13707, row13708, row13709, row15243, row15244, row15245, row15246, row15247, row15248, row13710, row13711, row13712, row13713, row13714, row13715, row15576, row15577, row15578, row13728, row13729, row13730]

theorem entryCheck14_3 : entry14_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_3 k)) := by decide +kernel

theorem rowsSound14_3 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval15234 x
  · exact rowEval15235 x
  · exact rowEval15236 x
  · exact rowEval15237 x
  · exact rowEval15238 x
  · exact rowEval15239 x
  · exact rowEval15573 x
  · exact rowEval15574 x
  · exact rowEval15575 x
  · exact rowEval13701 x
  · exact rowEval13702 x
  · exact rowEval13703 x
  · exact rowEval13704 x
  · exact rowEval13705 x
  · exact rowEval13706 x
  · exact rowEval13707 x
  · exact rowEval13708 x
  · exact rowEval13709 x
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
  · exact rowEval15576 x
  · exact rowEval15577 x
  · exact rowEval15578 x
  · exact rowEval13728 x
  · exact rowEval13729 x
  · exact rowEval13730 x

theorem entryEval14_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_3 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck14_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_3]

def rows14_4 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15252, row15253, row15254, row15255, row15256, row15257, row15579, row15580, row15581, row13737, row13738, row13739, row13740, row13741, row13742, row13743, row13744, row13745, row15261, row15262, row15263, row15264, row15265, row15266, row13746, row13747, row13748, row13749, row13750, row13751, row15582, row15583, row15584, row13764, row13765, row13766]

theorem entryCheck14_4 : entry14_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_4 k)) := by decide +kernel

theorem rowsSound14_4 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval15252 x
  · exact rowEval15253 x
  · exact rowEval15254 x
  · exact rowEval15255 x
  · exact rowEval15256 x
  · exact rowEval15257 x
  · exact rowEval15579 x
  · exact rowEval15580 x
  · exact rowEval15581 x
  · exact rowEval13737 x
  · exact rowEval13738 x
  · exact rowEval13739 x
  · exact rowEval13740 x
  · exact rowEval13741 x
  · exact rowEval13742 x
  · exact rowEval13743 x
  · exact rowEval13744 x
  · exact rowEval13745 x
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
  · exact rowEval15582 x
  · exact rowEval15583 x
  · exact rowEval15584 x
  · exact rowEval13764 x
  · exact rowEval13765 x
  · exact rowEval13766 x

theorem entryEval14_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_4 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck14_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_4]

def rows14_5 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15270, row15271, row15272, row15273, row15274, row15275, row15585, row15586, row15587, row13773, row13774, row13775, row13776, row13777, row13778, row13779, row13780, row13781, row15279, row15280, row15281, row15282, row15283, row15284, row13782, row13783, row13784, row13785, row13786, row13787, row15588, row15589, row15590, row13800, row13801, row13802]

theorem entryCheck14_5 : entry14_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_5 k)) := by decide +kernel

theorem rowsSound14_5 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval15270 x
  · exact rowEval15271 x
  · exact rowEval15272 x
  · exact rowEval15273 x
  · exact rowEval15274 x
  · exact rowEval15275 x
  · exact rowEval15585 x
  · exact rowEval15586 x
  · exact rowEval15587 x
  · exact rowEval13773 x
  · exact rowEval13774 x
  · exact rowEval13775 x
  · exact rowEval13776 x
  · exact rowEval13777 x
  · exact rowEval13778 x
  · exact rowEval13779 x
  · exact rowEval13780 x
  · exact rowEval13781 x
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
  · exact rowEval15588 x
  · exact rowEval15589 x
  · exact rowEval15590 x
  · exact rowEval13800 x
  · exact rowEval13801 x
  · exact rowEval13802 x

theorem entryEval14_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_5 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck14_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_5]

def rows14_6 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15288, row15289, row15290, row15291, row15292, row15293, row15591, row15592, row15593, row13809, row13810, row13811, row13812, row13813, row13814, row13815, row13816, row13817, row15297, row15298, row15299, row15300, row15301, row15302, row13818, row13819, row13820, row13821, row13822, row13823, row15594, row15595, row15596, row13836, row13837, row13838]

theorem entryCheck14_6 : entry14_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_6 k)) := by decide +kernel

theorem rowsSound14_6 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval15288 x
  · exact rowEval15289 x
  · exact rowEval15290 x
  · exact rowEval15291 x
  · exact rowEval15292 x
  · exact rowEval15293 x
  · exact rowEval15591 x
  · exact rowEval15592 x
  · exact rowEval15593 x
  · exact rowEval13809 x
  · exact rowEval13810 x
  · exact rowEval13811 x
  · exact rowEval13812 x
  · exact rowEval13813 x
  · exact rowEval13814 x
  · exact rowEval13815 x
  · exact rowEval13816 x
  · exact rowEval13817 x
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
  · exact rowEval15594 x
  · exact rowEval15595 x
  · exact rowEval15596 x
  · exact rowEval13836 x
  · exact rowEval13837 x
  · exact rowEval13838 x

theorem entryEval14_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_6 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck14_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_6]

def rows14_7 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15306, row15307, row15308, row15309, row15310, row15311, row15597, row15598, row15599, row15315, row15316, row15317, row15318, row15319, row15320, row15600, row15601, row15602, row15321, row15322, row15323, row15324, row15325, row15326, row15327, row15328, row15329, row15330, row15331, row15332, row15603, row15604, row15605, row15606, row15607, row15608]

theorem entryCheck14_7 : entry14_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_7 k)) := by decide +kernel

theorem rowsSound14_7 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval15306 x
  · exact rowEval15307 x
  · exact rowEval15308 x
  · exact rowEval15309 x
  · exact rowEval15310 x
  · exact rowEval15311 x
  · exact rowEval15597 x
  · exact rowEval15598 x
  · exact rowEval15599 x
  · exact rowEval15315 x
  · exact rowEval15316 x
  · exact rowEval15317 x
  · exact rowEval15318 x
  · exact rowEval15319 x
  · exact rowEval15320 x
  · exact rowEval15600 x
  · exact rowEval15601 x
  · exact rowEval15602 x
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
  · exact rowEval15603 x
  · exact rowEval15604 x
  · exact rowEval15605 x
  · exact rowEval15606 x
  · exact rowEval15607 x
  · exact rowEval15608 x

theorem entryEval14_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_7 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck14_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_7]

def rows14_8 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15342, row15343, row15344, row15345, row15346, row15347, row15609, row15610, row15611, row15351, row15352, row15353, row15354, row15355, row15356, row15612, row15613, row15614, row15357, row15358, row15359, row15360, row15361, row15362, row15363, row15364, row15365, row15366, row15367, row15368, row15615, row15616, row15617, row15618, row15619, row15620]

theorem entryCheck14_8 : entry14_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_8 k)) := by decide +kernel

theorem rowsSound14_8 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval15342 x
  · exact rowEval15343 x
  · exact rowEval15344 x
  · exact rowEval15345 x
  · exact rowEval15346 x
  · exact rowEval15347 x
  · exact rowEval15609 x
  · exact rowEval15610 x
  · exact rowEval15611 x
  · exact rowEval15351 x
  · exact rowEval15352 x
  · exact rowEval15353 x
  · exact rowEval15354 x
  · exact rowEval15355 x
  · exact rowEval15356 x
  · exact rowEval15612 x
  · exact rowEval15613 x
  · exact rowEval15614 x
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
  · exact rowEval15615 x
  · exact rowEval15616 x
  · exact rowEval15617 x
  · exact rowEval15618 x
  · exact rowEval15619 x
  · exact rowEval15620 x

theorem entryEval14_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_8 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck14_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_8]

def rows14_9 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15378, row15379, row15380, row15381, row15382, row15383, row15621, row15622, row15623, row15387, row15388, row15389, row15390, row15391, row15392, row15624, row15625, row15626, row15393, row15394, row15395, row15396, row15397, row15398, row15399, row15400, row15401, row15402, row15403, row15404, row15627, row15628, row15629, row15630, row15631, row15632]

theorem entryCheck14_9 : entry14_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_9 k)) := by decide +kernel

theorem rowsSound14_9 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval15378 x
  · exact rowEval15379 x
  · exact rowEval15380 x
  · exact rowEval15381 x
  · exact rowEval15382 x
  · exact rowEval15383 x
  · exact rowEval15621 x
  · exact rowEval15622 x
  · exact rowEval15623 x
  · exact rowEval15387 x
  · exact rowEval15388 x
  · exact rowEval15389 x
  · exact rowEval15390 x
  · exact rowEval15391 x
  · exact rowEval15392 x
  · exact rowEval15624 x
  · exact rowEval15625 x
  · exact rowEval15626 x
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
  · exact rowEval15627 x
  · exact rowEval15628 x
  · exact rowEval15629 x
  · exact rowEval15630 x
  · exact rowEval15631 x
  · exact rowEval15632 x

theorem entryEval14_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_9 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck14_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_9]

def rows14_10 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15414, row15415, row15416, row15417, row15418, row15419, row15633, row15634, row15635, row15423, row15424, row15425, row15426, row15427, row15428, row15636, row15637, row15638, row15429, row15430, row15431, row15432, row15433, row15434, row15435, row15436, row15437, row15438, row15439, row15440, row15639, row15640, row15641, row15642, row15643, row15644]

theorem entryCheck14_10 : entry14_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_10 k)) := by decide +kernel

theorem rowsSound14_10 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval15414 x
  · exact rowEval15415 x
  · exact rowEval15416 x
  · exact rowEval15417 x
  · exact rowEval15418 x
  · exact rowEval15419 x
  · exact rowEval15633 x
  · exact rowEval15634 x
  · exact rowEval15635 x
  · exact rowEval15423 x
  · exact rowEval15424 x
  · exact rowEval15425 x
  · exact rowEval15426 x
  · exact rowEval15427 x
  · exact rowEval15428 x
  · exact rowEval15636 x
  · exact rowEval15637 x
  · exact rowEval15638 x
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
  · exact rowEval15639 x
  · exact rowEval15640 x
  · exact rowEval15641 x
  · exact rowEval15642 x
  · exact rowEval15643 x
  · exact rowEval15644 x

theorem entryEval14_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_10 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck14_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_10]

def rows14_11 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15450, row15451, row15452, row15453, row15454, row15455, row15645, row15646, row15647, row15459, row15460, row15461, row15462, row15463, row15464, row15648, row15649, row15650, row15465, row15466, row15467, row15468, row15469, row15470, row15471, row15472, row15473, row15474, row15475, row15476, row15651, row15652, row15653, row15654, row15655, row15656]

theorem entryCheck14_11 : entry14_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_11 k)) := by decide +kernel

theorem rowsSound14_11 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval15450 x
  · exact rowEval15451 x
  · exact rowEval15452 x
  · exact rowEval15453 x
  · exact rowEval15454 x
  · exact rowEval15455 x
  · exact rowEval15645 x
  · exact rowEval15646 x
  · exact rowEval15647 x
  · exact rowEval15459 x
  · exact rowEval15460 x
  · exact rowEval15461 x
  · exact rowEval15462 x
  · exact rowEval15463 x
  · exact rowEval15464 x
  · exact rowEval15648 x
  · exact rowEval15649 x
  · exact rowEval15650 x
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
  · exact rowEval15651 x
  · exact rowEval15652 x
  · exact rowEval15653 x
  · exact rowEval15654 x
  · exact rowEval15655 x
  · exact rowEval15656 x

theorem entryEval14_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_11 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck14_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_11]

def rows14_12 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15486, row15487, row15488, row15489, row15490, row15491, row15657, row15658, row15659, row15495, row15496, row15497, row15498, row15499, row15500, row15660, row15661, row15662, row15501, row15502, row15503, row15504, row15505, row15506, row15507, row15508, row15509, row15510, row15511, row15512, row15663, row15664, row15665, row15666, row15667, row15668]

theorem entryCheck14_12 : entry14_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_12 k)) := by decide +kernel

theorem rowsSound14_12 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval15486 x
  · exact rowEval15487 x
  · exact rowEval15488 x
  · exact rowEval15489 x
  · exact rowEval15490 x
  · exact rowEval15491 x
  · exact rowEval15657 x
  · exact rowEval15658 x
  · exact rowEval15659 x
  · exact rowEval15495 x
  · exact rowEval15496 x
  · exact rowEval15497 x
  · exact rowEval15498 x
  · exact rowEval15499 x
  · exact rowEval15500 x
  · exact rowEval15660 x
  · exact rowEval15661 x
  · exact rowEval15662 x
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
  · exact rowEval15663 x
  · exact rowEval15664 x
  · exact rowEval15665 x
  · exact rowEval15666 x
  · exact rowEval15667 x
  · exact rowEval15668 x

theorem entryEval14_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_12 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck14_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_12]

def rows14_13 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15522, row15523, row15524, row15525, row15526, row15527, row15669, row15670, row15671, row15531, row15532, row15533, row15534, row15535, row15536, row15672, row15673, row15674, row15537, row15538, row15539, row15540, row15541, row15542, row15543, row15544, row15545, row15546, row15547, row15548, row15675, row15676, row15677, row15678, row15679, row15680]

theorem entryCheck14_13 : entry14_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_13 k)) := by decide +kernel

theorem rowsSound14_13 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval15522 x
  · exact rowEval15523 x
  · exact rowEval15524 x
  · exact rowEval15525 x
  · exact rowEval15526 x
  · exact rowEval15527 x
  · exact rowEval15669 x
  · exact rowEval15670 x
  · exact rowEval15671 x
  · exact rowEval15531 x
  · exact rowEval15532 x
  · exact rowEval15533 x
  · exact rowEval15534 x
  · exact rowEval15535 x
  · exact rowEval15536 x
  · exact rowEval15672 x
  · exact rowEval15673 x
  · exact rowEval15674 x
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
  · exact rowEval15675 x
  · exact rowEval15676 x
  · exact rowEval15677 x
  · exact rowEval15678 x
  · exact rowEval15679 x
  · exact rowEval15680 x

theorem entryEval14_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_13 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck14_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_13]

def rows14_14 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15681, row15682, row15683, row15684, row15685, row15686, row15687, row15688, row15689, row15690, row15691, row15692, row15693, row15694, row15695, row15696, row15697, row15698, row15699, row15700, row15701, row15702, row15703, row15704, row15705, row15706, row15707, row15708, row15709, row15710, row15711, row15712, row15713, row15714, row15715, row15716]

theorem entryCheck14_14 : entry14_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form14.terms k).coefficient) (rows14_14 k)) := by decide +kernel

theorem rowsSound14_14 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form14) x := by
  fin_cases k
  · exact rowEval15681 x
  · exact rowEval15682 x
  · exact rowEval15683 x
  · exact rowEval15684 x
  · exact rowEval15685 x
  · exact rowEval15686 x
  · exact rowEval15687 x
  · exact rowEval15688 x
  · exact rowEval15689 x
  · exact rowEval15690 x
  · exact rowEval15691 x
  · exact rowEval15692 x
  · exact rowEval15693 x
  · exact rowEval15694 x
  · exact rowEval15695 x
  · exact rowEval15696 x
  · exact rowEval15697 x
  · exact rowEval15698 x
  · exact rowEval15699 x
  · exact rowEval15700 x
  · exact rowEval15701 x
  · exact rowEval15702 x
  · exact rowEval15703 x
  · exact rowEval15704 x
  · exact rowEval15705 x
  · exact rowEval15706 x
  · exact rowEval15707 x
  · exact rowEval15708 x
  · exact rowEval15709 x
  · exact rowEval15710 x
  · exact rowEval15711 x
  · exact rowEval15712 x
  · exact rowEval15713 x
  · exact rowEval15714 x
  · exact rowEval15715 x
  · exact rowEval15716 x

theorem entryEval14_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_14 (GramNormalization.eval B) = GramFunctions.Block4.form14.mixedGram GramFunctions.Block4.form14 B := by
  rw [entryCheck14_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form14 GramFunctions.Block4.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_14]

end MUB6.Certificate.GramEntries.Block4

end OAI
