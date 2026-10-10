import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block154
import OAI.Analysis.MutuallyUnbiased.GramRows.Block155
import OAI.Analysis.MutuallyUnbiased.GramRows.Block156
import OAI.Analysis.MutuallyUnbiased.GramRows.Block157

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_0 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16707, row16708, row16709, row16710, row16711, row16712, row16713, row16714, row16715, row16716, row16717, row16718, row16719, row16720, row16721, row16722, row16723, row16724]

theorem entryCheck17_0 : entry17_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_0 k)) := by decide +kernel

theorem rowsSound17_0 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval16707 x
  · exact rowEval16708 x
  · exact rowEval16709 x
  · exact rowEval16710 x
  · exact rowEval16711 x
  · exact rowEval16712 x
  · exact rowEval16713 x
  · exact rowEval16714 x
  · exact rowEval16715 x
  · exact rowEval16716 x
  · exact rowEval16717 x
  · exact rowEval16718 x
  · exact rowEval16719 x
  · exact rowEval16720 x
  · exact rowEval16721 x
  · exact rowEval16722 x
  · exact rowEval16723 x
  · exact rowEval16724 x

theorem entryEval17_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_0 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck17_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_0]

def rows17_1 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16725, row16726, row16727, row16728, row16729, row16730, row16731, row16732, row16733, row16734, row16735, row16736, row16737, row16738, row16739, row16740, row16741, row16742]

theorem entryCheck17_1 : entry17_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_1 k)) := by decide +kernel

theorem rowsSound17_1 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval16725 x
  · exact rowEval16726 x
  · exact rowEval16727 x
  · exact rowEval16728 x
  · exact rowEval16729 x
  · exact rowEval16730 x
  · exact rowEval16731 x
  · exact rowEval16732 x
  · exact rowEval16733 x
  · exact rowEval16734 x
  · exact rowEval16735 x
  · exact rowEval16736 x
  · exact rowEval16737 x
  · exact rowEval16738 x
  · exact rowEval16739 x
  · exact rowEval16740 x
  · exact rowEval16741 x
  · exact rowEval16742 x

theorem entryEval17_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_1 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck17_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_1]

def rows17_2 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16743, row16744, row16745, row16746, row16747, row16748, row16749, row16750, row16751, row16752, row16753, row16754, row16755, row16756, row16757, row16758, row16759, row16760]

theorem entryCheck17_2 : entry17_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_2 k)) := by decide +kernel

theorem rowsSound17_2 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval16743 x
  · exact rowEval16744 x
  · exact rowEval16745 x
  · exact rowEval16746 x
  · exact rowEval16747 x
  · exact rowEval16748 x
  · exact rowEval16749 x
  · exact rowEval16750 x
  · exact rowEval16751 x
  · exact rowEval16752 x
  · exact rowEval16753 x
  · exact rowEval16754 x
  · exact rowEval16755 x
  · exact rowEval16756 x
  · exact rowEval16757 x
  · exact rowEval16758 x
  · exact rowEval16759 x
  · exact rowEval16760 x

theorem entryEval17_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_2 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck17_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_2]

def rows17_3 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16761, row16762, row16763, row16764, row16765, row16766, row16767, row16768, row16769, row16770, row16771, row16772, row16773, row16774, row16775, row16776, row16777, row16778]

theorem entryCheck17_3 : entry17_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_3 k)) := by decide +kernel

theorem rowsSound17_3 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval16761 x
  · exact rowEval16762 x
  · exact rowEval16763 x
  · exact rowEval16764 x
  · exact rowEval16765 x
  · exact rowEval16766 x
  · exact rowEval16767 x
  · exact rowEval16768 x
  · exact rowEval16769 x
  · exact rowEval16770 x
  · exact rowEval16771 x
  · exact rowEval16772 x
  · exact rowEval16773 x
  · exact rowEval16774 x
  · exact rowEval16775 x
  · exact rowEval16776 x
  · exact rowEval16777 x
  · exact rowEval16778 x

theorem entryEval17_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_3 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck17_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_3]

def rows17_4 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16779, row16780, row16781, row16782, row16783, row16784, row16785, row16786, row16787, row16788, row16789, row16790, row16791, row16792, row16793, row16794, row16795, row16796]

theorem entryCheck17_4 : entry17_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_4 k)) := by decide +kernel

theorem rowsSound17_4 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval16779 x
  · exact rowEval16780 x
  · exact rowEval16781 x
  · exact rowEval16782 x
  · exact rowEval16783 x
  · exact rowEval16784 x
  · exact rowEval16785 x
  · exact rowEval16786 x
  · exact rowEval16787 x
  · exact rowEval16788 x
  · exact rowEval16789 x
  · exact rowEval16790 x
  · exact rowEval16791 x
  · exact rowEval16792 x
  · exact rowEval16793 x
  · exact rowEval16794 x
  · exact rowEval16795 x
  · exact rowEval16796 x

theorem entryEval17_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_4 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck17_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_4]

def rows17_5 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16797, row16798, row16799, row16800, row16801, row16802, row16803, row16804, row16805, row16806, row16807, row16808, row16809, row16810, row16811, row16812, row16813, row16814]

theorem entryCheck17_5 : entry17_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_5 k)) := by decide +kernel

theorem rowsSound17_5 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval16797 x
  · exact rowEval16798 x
  · exact rowEval16799 x
  · exact rowEval16800 x
  · exact rowEval16801 x
  · exact rowEval16802 x
  · exact rowEval16803 x
  · exact rowEval16804 x
  · exact rowEval16805 x
  · exact rowEval16806 x
  · exact rowEval16807 x
  · exact rowEval16808 x
  · exact rowEval16809 x
  · exact rowEval16810 x
  · exact rowEval16811 x
  · exact rowEval16812 x
  · exact rowEval16813 x
  · exact rowEval16814 x

theorem entryEval17_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_5 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck17_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_5]

def rows17_6 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16815, row16816, row16817, row16818, row16819, row16820, row16821, row16822, row16823, row16824, row16825, row16826, row16827, row16828, row16829, row16830, row16831, row16832]

theorem entryCheck17_6 : entry17_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_6 k)) := by decide +kernel

theorem rowsSound17_6 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval16815 x
  · exact rowEval16816 x
  · exact rowEval16817 x
  · exact rowEval16818 x
  · exact rowEval16819 x
  · exact rowEval16820 x
  · exact rowEval16821 x
  · exact rowEval16822 x
  · exact rowEval16823 x
  · exact rowEval16824 x
  · exact rowEval16825 x
  · exact rowEval16826 x
  · exact rowEval16827 x
  · exact rowEval16828 x
  · exact rowEval16829 x
  · exact rowEval16830 x
  · exact rowEval16831 x
  · exact rowEval16832 x

theorem entryEval17_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_6 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck17_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_6]

def rows17_7 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16833, row16834, row16835, row16836, row16837, row16838, row16839, row16840, row16841, row16842, row16843, row16844, row16845, row16846, row16847, row16848, row16849, row16850]

theorem entryCheck17_7 : entry17_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_7 k)) := by decide +kernel

theorem rowsSound17_7 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval16833 x
  · exact rowEval16834 x
  · exact rowEval16835 x
  · exact rowEval16836 x
  · exact rowEval16837 x
  · exact rowEval16838 x
  · exact rowEval16839 x
  · exact rowEval16840 x
  · exact rowEval16841 x
  · exact rowEval16842 x
  · exact rowEval16843 x
  · exact rowEval16844 x
  · exact rowEval16845 x
  · exact rowEval16846 x
  · exact rowEval16847 x
  · exact rowEval16848 x
  · exact rowEval16849 x
  · exact rowEval16850 x

theorem entryEval17_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_7 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck17_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_7]

def rows17_8 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16851, row16852, row16853, row16854, row16855, row16856, row16857, row16858, row16859, row16860, row16861, row16862, row16863, row16864, row16865, row16866, row16867, row16868]

theorem entryCheck17_8 : entry17_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_8 k)) := by decide +kernel

theorem rowsSound17_8 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval16851 x
  · exact rowEval16852 x
  · exact rowEval16853 x
  · exact rowEval16854 x
  · exact rowEval16855 x
  · exact rowEval16856 x
  · exact rowEval16857 x
  · exact rowEval16858 x
  · exact rowEval16859 x
  · exact rowEval16860 x
  · exact rowEval16861 x
  · exact rowEval16862 x
  · exact rowEval16863 x
  · exact rowEval16864 x
  · exact rowEval16865 x
  · exact rowEval16866 x
  · exact rowEval16867 x
  · exact rowEval16868 x

theorem entryEval17_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_8 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck17_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_8]

def rows17_9 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16869, row16870, row16871, row16872, row16873, row16874, row16875, row16876, row16877, row16878, row16879, row16880, row16881, row16882, row16883, row16884, row16885, row16886]

theorem entryCheck17_9 : entry17_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_9 k)) := by decide +kernel

theorem rowsSound17_9 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval16869 x
  · exact rowEval16870 x
  · exact rowEval16871 x
  · exact rowEval16872 x
  · exact rowEval16873 x
  · exact rowEval16874 x
  · exact rowEval16875 x
  · exact rowEval16876 x
  · exact rowEval16877 x
  · exact rowEval16878 x
  · exact rowEval16879 x
  · exact rowEval16880 x
  · exact rowEval16881 x
  · exact rowEval16882 x
  · exact rowEval16883 x
  · exact rowEval16884 x
  · exact rowEval16885 x
  · exact rowEval16886 x

theorem entryEval17_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_9 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck17_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_9]

def rows17_10 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16887, row16888, row16889, row16890, row16891, row16892, row16893, row16894, row16895, row16896, row16897, row16898, row16899, row16900, row16901, row16902, row16903, row16904]

theorem entryCheck17_10 : entry17_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_10 k)) := by decide +kernel

theorem rowsSound17_10 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval16887 x
  · exact rowEval16888 x
  · exact rowEval16889 x
  · exact rowEval16890 x
  · exact rowEval16891 x
  · exact rowEval16892 x
  · exact rowEval16893 x
  · exact rowEval16894 x
  · exact rowEval16895 x
  · exact rowEval16896 x
  · exact rowEval16897 x
  · exact rowEval16898 x
  · exact rowEval16899 x
  · exact rowEval16900 x
  · exact rowEval16901 x
  · exact rowEval16902 x
  · exact rowEval16903 x
  · exact rowEval16904 x

theorem entryEval17_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_10 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck17_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_10]

def rows17_11 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16905, row16906, row16907, row16908, row16909, row16910, row16911, row16912, row16913, row16914, row16915, row16916, row16917, row16918, row16919, row16920, row16921, row16922]

theorem entryCheck17_11 : entry17_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_11 k)) := by decide +kernel

theorem rowsSound17_11 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval16905 x
  · exact rowEval16906 x
  · exact rowEval16907 x
  · exact rowEval16908 x
  · exact rowEval16909 x
  · exact rowEval16910 x
  · exact rowEval16911 x
  · exact rowEval16912 x
  · exact rowEval16913 x
  · exact rowEval16914 x
  · exact rowEval16915 x
  · exact rowEval16916 x
  · exact rowEval16917 x
  · exact rowEval16918 x
  · exact rowEval16919 x
  · exact rowEval16920 x
  · exact rowEval16921 x
  · exact rowEval16922 x

theorem entryEval17_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_11 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck17_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_11]

def rows17_12 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16923, row16924, row16925, row16926, row16927, row16928, row16929, row16930, row16931, row16932, row16933, row16934, row16935, row16936, row16937, row16938, row16939, row16940]

theorem entryCheck17_12 : entry17_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_12 k)) := by decide +kernel

theorem rowsSound17_12 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval16923 x
  · exact rowEval16924 x
  · exact rowEval16925 x
  · exact rowEval16926 x
  · exact rowEval16927 x
  · exact rowEval16928 x
  · exact rowEval16929 x
  · exact rowEval16930 x
  · exact rowEval16931 x
  · exact rowEval16932 x
  · exact rowEval16933 x
  · exact rowEval16934 x
  · exact rowEval16935 x
  · exact rowEval16936 x
  · exact rowEval16937 x
  · exact rowEval16938 x
  · exact rowEval16939 x
  · exact rowEval16940 x

theorem entryEval17_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_12 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck17_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_12]

def rows17_13 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16941, row16942, row16943, row16944, row16945, row16946, row16947, row16948, row16949, row16950, row16951, row16952, row16953, row16954, row16955, row16956, row16957, row16958]

theorem entryCheck17_13 : entry17_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_13 k)) := by decide +kernel

theorem rowsSound17_13 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval16941 x
  · exact rowEval16942 x
  · exact rowEval16943 x
  · exact rowEval16944 x
  · exact rowEval16945 x
  · exact rowEval16946 x
  · exact rowEval16947 x
  · exact rowEval16948 x
  · exact rowEval16949 x
  · exact rowEval16950 x
  · exact rowEval16951 x
  · exact rowEval16952 x
  · exact rowEval16953 x
  · exact rowEval16954 x
  · exact rowEval16955 x
  · exact rowEval16956 x
  · exact rowEval16957 x
  · exact rowEval16958 x

theorem entryEval17_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_13 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck17_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_13]

def rows17_14 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16959, row16960, row16961, row16962, row16963, row16964, row16965, row16966, row16967, row16968, row16969, row16970, row16971, row16972, row16973, row16974, row16975, row16976]

theorem entryCheck17_14 : entry17_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_14 k)) := by decide +kernel

theorem rowsSound17_14 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form14) x := by
  fin_cases k
  · exact rowEval16959 x
  · exact rowEval16960 x
  · exact rowEval16961 x
  · exact rowEval16962 x
  · exact rowEval16963 x
  · exact rowEval16964 x
  · exact rowEval16965 x
  · exact rowEval16966 x
  · exact rowEval16967 x
  · exact rowEval16968 x
  · exact rowEval16969 x
  · exact rowEval16970 x
  · exact rowEval16971 x
  · exact rowEval16972 x
  · exact rowEval16973 x
  · exact rowEval16974 x
  · exact rowEval16975 x
  · exact rowEval16976 x

theorem entryEval17_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_14 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form14 B := by
  rw [entryCheck17_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_14]

def rows17_15 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16977, row16978, row16979, row16980, row16981, row16982, row16983, row16984, row16985, row16986, row16987, row16988, row16989, row16990, row16991, row16992, row16993, row16994]

theorem entryCheck17_15 : entry17_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_15 k)) := by decide +kernel

theorem rowsSound17_15 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form15) x := by
  fin_cases k
  · exact rowEval16977 x
  · exact rowEval16978 x
  · exact rowEval16979 x
  · exact rowEval16980 x
  · exact rowEval16981 x
  · exact rowEval16982 x
  · exact rowEval16983 x
  · exact rowEval16984 x
  · exact rowEval16985 x
  · exact rowEval16986 x
  · exact rowEval16987 x
  · exact rowEval16988 x
  · exact rowEval16989 x
  · exact rowEval16990 x
  · exact rowEval16991 x
  · exact rowEval16992 x
  · exact rowEval16993 x
  · exact rowEval16994 x

theorem entryEval17_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_15 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form15 B := by
  rw [entryCheck17_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_15]

def rows17_16 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16995, row16996, row16997, row16998, row16999, row17000, row17001, row17002, row17003, row17004, row17005, row17006, row17007, row17008, row17009, row17010, row17011, row17012]

theorem entryCheck17_16 : entry17_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_16 k)) := by decide +kernel

theorem rowsSound17_16 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form16) x := by
  fin_cases k
  · exact rowEval16995 x
  · exact rowEval16996 x
  · exact rowEval16997 x
  · exact rowEval16998 x
  · exact rowEval16999 x
  · exact rowEval17000 x
  · exact rowEval17001 x
  · exact rowEval17002 x
  · exact rowEval17003 x
  · exact rowEval17004 x
  · exact rowEval17005 x
  · exact rowEval17006 x
  · exact rowEval17007 x
  · exact rowEval17008 x
  · exact rowEval17009 x
  · exact rowEval17010 x
  · exact rowEval17011 x
  · exact rowEval17012 x

theorem entryEval17_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_16 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form16 B := by
  rw [entryCheck17_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_16]

def rows17_17 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row17013, row17014, row17015, row17016, row17017, row17018, row17019, row17020, row17021, row17022, row17023, row17024, row17025, row17026, row17027, row17028, row17029, row17030]

theorem entryCheck17_17 : entry17_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_17 k)) := by decide +kernel

theorem rowsSound17_17 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval17013 x
  · exact rowEval17014 x
  · exact rowEval17015 x
  · exact rowEval17016 x
  · exact rowEval17017 x
  · exact rowEval17018 x
  · exact rowEval17019 x
  · exact rowEval17020 x
  · exact rowEval17021 x
  · exact rowEval17022 x
  · exact rowEval17023 x
  · exact rowEval17024 x
  · exact rowEval17025 x
  · exact rowEval17026 x
  · exact rowEval17027 x
  · exact rowEval17028 x
  · exact rowEval17029 x
  · exact rowEval17030 x

theorem entryEval17_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_17 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck17_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_17]

end MUB6.Certificate.GramEntries.Block4

end OAI
