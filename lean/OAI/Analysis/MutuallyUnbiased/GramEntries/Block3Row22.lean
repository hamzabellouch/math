import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block107
import OAI.Analysis.MutuallyUnbiased.GramRows.Block108
import OAI.Analysis.MutuallyUnbiased.GramRows.Block109
import OAI.Analysis.MutuallyUnbiased.GramRows.Block110
import OAI.Analysis.MutuallyUnbiased.GramRows.Block111
import OAI.Analysis.MutuallyUnbiased.GramRows.Block112
import OAI.Analysis.MutuallyUnbiased.GramRows.Block113
import OAI.Analysis.MutuallyUnbiased.GramRows.Block114
import OAI.Analysis.MutuallyUnbiased.GramRows.Block115
import OAI.Analysis.MutuallyUnbiased.GramRows.Block116

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows22_0 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11486, row11487, row11488, row11489, row11490, row11491, row11492, row11493, row11494, row11495, row11496, row11497, row10694, row10695, row10696, row10697, row10698, row10699, row10700, row10701, row10702, row10703, row10704, row10705, row10706, row10707, row10708, row10709, row10710, row10711, row10712, row10713, row10714, row10715, row10716, row10717]

theorem entryCheck22_0 : entry22_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_0 k)) := by decide +kernel

theorem rowsSound22_0 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval11486 x
  · exact rowEval11487 x
  · exact rowEval11488 x
  · exact rowEval11489 x
  · exact rowEval11490 x
  · exact rowEval11491 x
  · exact rowEval11492 x
  · exact rowEval11493 x
  · exact rowEval11494 x
  · exact rowEval11495 x
  · exact rowEval11496 x
  · exact rowEval11497 x
  · exact rowEval10694 x
  · exact rowEval10695 x
  · exact rowEval10696 x
  · exact rowEval10697 x
  · exact rowEval10698 x
  · exact rowEval10699 x
  · exact rowEval10700 x
  · exact rowEval10701 x
  · exact rowEval10702 x
  · exact rowEval10703 x
  · exact rowEval10704 x
  · exact rowEval10705 x
  · exact rowEval10706 x
  · exact rowEval10707 x
  · exact rowEval10708 x
  · exact rowEval10709 x
  · exact rowEval10710 x
  · exact rowEval10711 x
  · exact rowEval10712 x
  · exact rowEval10713 x
  · exact rowEval10714 x
  · exact rowEval10715 x
  · exact rowEval10716 x
  · exact rowEval10717 x

theorem entryEval22_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_0 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck22_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_0]

def rows22_1 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11498, row11499, row11500, row11501, row11502, row11503, row11504, row11505, row11506, row11507, row11508, row11509, row10730, row10731, row10732, row10733, row10734, row10735, row10736, row10737, row10738, row10739, row10740, row10741, row10742, row10743, row10744, row10745, row10746, row10747, row10748, row10749, row10750, row10751, row10752, row10753]

theorem entryCheck22_1 : entry22_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_1 k)) := by decide +kernel

theorem rowsSound22_1 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval11498 x
  · exact rowEval11499 x
  · exact rowEval11500 x
  · exact rowEval11501 x
  · exact rowEval11502 x
  · exact rowEval11503 x
  · exact rowEval11504 x
  · exact rowEval11505 x
  · exact rowEval11506 x
  · exact rowEval11507 x
  · exact rowEval11508 x
  · exact rowEval11509 x
  · exact rowEval10730 x
  · exact rowEval10731 x
  · exact rowEval10732 x
  · exact rowEval10733 x
  · exact rowEval10734 x
  · exact rowEval10735 x
  · exact rowEval10736 x
  · exact rowEval10737 x
  · exact rowEval10738 x
  · exact rowEval10739 x
  · exact rowEval10740 x
  · exact rowEval10741 x
  · exact rowEval10742 x
  · exact rowEval10743 x
  · exact rowEval10744 x
  · exact rowEval10745 x
  · exact rowEval10746 x
  · exact rowEval10747 x
  · exact rowEval10748 x
  · exact rowEval10749 x
  · exact rowEval10750 x
  · exact rowEval10751 x
  · exact rowEval10752 x
  · exact rowEval10753 x

theorem entryEval22_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_1 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck22_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_1]

def rows22_2 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11510, row11511, row11512, row11513, row11514, row11515, row11516, row11517, row11518, row11519, row11520, row11521, row10766, row10767, row10768, row10769, row10770, row10771, row10772, row10773, row10774, row10775, row10776, row10777, row10778, row10779, row10780, row10781, row10782, row10783, row10784, row10785, row10786, row10787, row10788, row10789]

theorem entryCheck22_2 : entry22_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_2 k)) := by decide +kernel

theorem rowsSound22_2 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval11510 x
  · exact rowEval11511 x
  · exact rowEval11512 x
  · exact rowEval11513 x
  · exact rowEval11514 x
  · exact rowEval11515 x
  · exact rowEval11516 x
  · exact rowEval11517 x
  · exact rowEval11518 x
  · exact rowEval11519 x
  · exact rowEval11520 x
  · exact rowEval11521 x
  · exact rowEval10766 x
  · exact rowEval10767 x
  · exact rowEval10768 x
  · exact rowEval10769 x
  · exact rowEval10770 x
  · exact rowEval10771 x
  · exact rowEval10772 x
  · exact rowEval10773 x
  · exact rowEval10774 x
  · exact rowEval10775 x
  · exact rowEval10776 x
  · exact rowEval10777 x
  · exact rowEval10778 x
  · exact rowEval10779 x
  · exact rowEval10780 x
  · exact rowEval10781 x
  · exact rowEval10782 x
  · exact rowEval10783 x
  · exact rowEval10784 x
  · exact rowEval10785 x
  · exact rowEval10786 x
  · exact rowEval10787 x
  · exact rowEval10788 x
  · exact rowEval10789 x

theorem entryEval22_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_2 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck22_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_2]

def rows22_3 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11522, row11523, row11524, row11525, row11526, row11527, row11528, row11529, row11530, row11531, row11532, row11533, row10802, row10803, row10804, row10805, row10806, row10807, row10808, row10809, row10810, row10811, row10812, row10813, row10814, row10815, row10816, row10817, row10818, row10819, row10820, row10821, row10822, row10823, row10824, row10825]

theorem entryCheck22_3 : entry22_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_3 k)) := by decide +kernel

theorem rowsSound22_3 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval11522 x
  · exact rowEval11523 x
  · exact rowEval11524 x
  · exact rowEval11525 x
  · exact rowEval11526 x
  · exact rowEval11527 x
  · exact rowEval11528 x
  · exact rowEval11529 x
  · exact rowEval11530 x
  · exact rowEval11531 x
  · exact rowEval11532 x
  · exact rowEval11533 x
  · exact rowEval10802 x
  · exact rowEval10803 x
  · exact rowEval10804 x
  · exact rowEval10805 x
  · exact rowEval10806 x
  · exact rowEval10807 x
  · exact rowEval10808 x
  · exact rowEval10809 x
  · exact rowEval10810 x
  · exact rowEval10811 x
  · exact rowEval10812 x
  · exact rowEval10813 x
  · exact rowEval10814 x
  · exact rowEval10815 x
  · exact rowEval10816 x
  · exact rowEval10817 x
  · exact rowEval10818 x
  · exact rowEval10819 x
  · exact rowEval10820 x
  · exact rowEval10821 x
  · exact rowEval10822 x
  · exact rowEval10823 x
  · exact rowEval10824 x
  · exact rowEval10825 x

theorem entryEval22_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_3 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck22_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_3]

def rows22_4 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11534, row11535, row11536, row11537, row11538, row11539, row11540, row11541, row11542, row11543, row11544, row11545, row10838, row10839, row10840, row10841, row10842, row10843, row10844, row10845, row10846, row10847, row10848, row10849, row10850, row10851, row10852, row10853, row10854, row10855, row10856, row10857, row10858, row10859, row10860, row10861]

theorem entryCheck22_4 : entry22_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_4 k)) := by decide +kernel

theorem rowsSound22_4 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval11534 x
  · exact rowEval11535 x
  · exact rowEval11536 x
  · exact rowEval11537 x
  · exact rowEval11538 x
  · exact rowEval11539 x
  · exact rowEval11540 x
  · exact rowEval11541 x
  · exact rowEval11542 x
  · exact rowEval11543 x
  · exact rowEval11544 x
  · exact rowEval11545 x
  · exact rowEval10838 x
  · exact rowEval10839 x
  · exact rowEval10840 x
  · exact rowEval10841 x
  · exact rowEval10842 x
  · exact rowEval10843 x
  · exact rowEval10844 x
  · exact rowEval10845 x
  · exact rowEval10846 x
  · exact rowEval10847 x
  · exact rowEval10848 x
  · exact rowEval10849 x
  · exact rowEval10850 x
  · exact rowEval10851 x
  · exact rowEval10852 x
  · exact rowEval10853 x
  · exact rowEval10854 x
  · exact rowEval10855 x
  · exact rowEval10856 x
  · exact rowEval10857 x
  · exact rowEval10858 x
  · exact rowEval10859 x
  · exact rowEval10860 x
  · exact rowEval10861 x

theorem entryEval22_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_4 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck22_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_4]

def rows22_5 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11546, row11547, row11548, row11549, row11550, row11551, row11552, row11553, row11554, row11555, row11556, row11557, row10874, row10875, row10876, row10877, row10878, row10879, row10880, row10881, row10882, row10883, row10884, row10885, row10886, row10887, row10888, row10889, row10890, row10891, row10892, row10893, row10894, row10895, row10896, row10897]

theorem entryCheck22_5 : entry22_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_5 k)) := by decide +kernel

theorem rowsSound22_5 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval11546 x
  · exact rowEval11547 x
  · exact rowEval11548 x
  · exact rowEval11549 x
  · exact rowEval11550 x
  · exact rowEval11551 x
  · exact rowEval11552 x
  · exact rowEval11553 x
  · exact rowEval11554 x
  · exact rowEval11555 x
  · exact rowEval11556 x
  · exact rowEval11557 x
  · exact rowEval10874 x
  · exact rowEval10875 x
  · exact rowEval10876 x
  · exact rowEval10877 x
  · exact rowEval10878 x
  · exact rowEval10879 x
  · exact rowEval10880 x
  · exact rowEval10881 x
  · exact rowEval10882 x
  · exact rowEval10883 x
  · exact rowEval10884 x
  · exact rowEval10885 x
  · exact rowEval10886 x
  · exact rowEval10887 x
  · exact rowEval10888 x
  · exact rowEval10889 x
  · exact rowEval10890 x
  · exact rowEval10891 x
  · exact rowEval10892 x
  · exact rowEval10893 x
  · exact rowEval10894 x
  · exact rowEval10895 x
  · exact rowEval10896 x
  · exact rowEval10897 x

theorem entryEval22_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_5 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck22_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_5]

def rows22_6 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11558, row11559, row11560, row11561, row11562, row11563, row11564, row11565, row11566, row11567, row11568, row11569, row10910, row10911, row10912, row10913, row10914, row10915, row10916, row10917, row10918, row10919, row10920, row10921, row10922, row10923, row10924, row10925, row10926, row10927, row10928, row10929, row10930, row10931, row10932, row10933]

theorem entryCheck22_6 : entry22_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_6 k)) := by decide +kernel

theorem rowsSound22_6 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval11558 x
  · exact rowEval11559 x
  · exact rowEval11560 x
  · exact rowEval11561 x
  · exact rowEval11562 x
  · exact rowEval11563 x
  · exact rowEval11564 x
  · exact rowEval11565 x
  · exact rowEval11566 x
  · exact rowEval11567 x
  · exact rowEval11568 x
  · exact rowEval11569 x
  · exact rowEval10910 x
  · exact rowEval10911 x
  · exact rowEval10912 x
  · exact rowEval10913 x
  · exact rowEval10914 x
  · exact rowEval10915 x
  · exact rowEval10916 x
  · exact rowEval10917 x
  · exact rowEval10918 x
  · exact rowEval10919 x
  · exact rowEval10920 x
  · exact rowEval10921 x
  · exact rowEval10922 x
  · exact rowEval10923 x
  · exact rowEval10924 x
  · exact rowEval10925 x
  · exact rowEval10926 x
  · exact rowEval10927 x
  · exact rowEval10928 x
  · exact rowEval10929 x
  · exact rowEval10930 x
  · exact rowEval10931 x
  · exact rowEval10932 x
  · exact rowEval10933 x

theorem entryEval22_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_6 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck22_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_6]

def rows22_7 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11570, row11571, row11572, row11573, row11574, row11575, row11576, row11577, row11578, row11579, row11580, row11581, row10946, row10947, row10948, row10949, row10950, row10951, row10952, row10953, row10954, row10955, row10956, row10957, row10958, row10959, row10960, row10961, row10962, row10963, row10964, row10965, row10966, row10967, row10968, row10969]

theorem entryCheck22_7 : entry22_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_7 k)) := by decide +kernel

theorem rowsSound22_7 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval11570 x
  · exact rowEval11571 x
  · exact rowEval11572 x
  · exact rowEval11573 x
  · exact rowEval11574 x
  · exact rowEval11575 x
  · exact rowEval11576 x
  · exact rowEval11577 x
  · exact rowEval11578 x
  · exact rowEval11579 x
  · exact rowEval11580 x
  · exact rowEval11581 x
  · exact rowEval10946 x
  · exact rowEval10947 x
  · exact rowEval10948 x
  · exact rowEval10949 x
  · exact rowEval10950 x
  · exact rowEval10951 x
  · exact rowEval10952 x
  · exact rowEval10953 x
  · exact rowEval10954 x
  · exact rowEval10955 x
  · exact rowEval10956 x
  · exact rowEval10957 x
  · exact rowEval10958 x
  · exact rowEval10959 x
  · exact rowEval10960 x
  · exact rowEval10961 x
  · exact rowEval10962 x
  · exact rowEval10963 x
  · exact rowEval10964 x
  · exact rowEval10965 x
  · exact rowEval10966 x
  · exact rowEval10967 x
  · exact rowEval10968 x
  · exact rowEval10969 x

theorem entryEval22_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_7 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck22_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_7]

def rows22_8 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11582, row11583, row11584, row11585, row11586, row11587, row11588, row11589, row11590, row11591, row11592, row11593, row10982, row10983, row10984, row10985, row10986, row10987, row10988, row10989, row10990, row10991, row10992, row10993, row10994, row10995, row10996, row10997, row10998, row10999, row11000, row11001, row11002, row11003, row11004, row11005]

theorem entryCheck22_8 : entry22_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_8 k)) := by decide +kernel

theorem rowsSound22_8 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval11582 x
  · exact rowEval11583 x
  · exact rowEval11584 x
  · exact rowEval11585 x
  · exact rowEval11586 x
  · exact rowEval11587 x
  · exact rowEval11588 x
  · exact rowEval11589 x
  · exact rowEval11590 x
  · exact rowEval11591 x
  · exact rowEval11592 x
  · exact rowEval11593 x
  · exact rowEval10982 x
  · exact rowEval10983 x
  · exact rowEval10984 x
  · exact rowEval10985 x
  · exact rowEval10986 x
  · exact rowEval10987 x
  · exact rowEval10988 x
  · exact rowEval10989 x
  · exact rowEval10990 x
  · exact rowEval10991 x
  · exact rowEval10992 x
  · exact rowEval10993 x
  · exact rowEval10994 x
  · exact rowEval10995 x
  · exact rowEval10996 x
  · exact rowEval10997 x
  · exact rowEval10998 x
  · exact rowEval10999 x
  · exact rowEval11000 x
  · exact rowEval11001 x
  · exact rowEval11002 x
  · exact rowEval11003 x
  · exact rowEval11004 x
  · exact rowEval11005 x

theorem entryEval22_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_8 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck22_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_8]

def rows22_9 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11594, row11595, row11596, row11597, row11598, row11599, row11600, row11601, row11602, row11603, row11604, row11605, row11018, row11019, row11020, row11021, row11022, row11023, row11024, row11025, row11026, row11027, row11028, row11029, row11030, row11031, row11032, row11033, row11034, row11035, row11036, row11037, row11038, row11039, row11040, row11041]

theorem entryCheck22_9 : entry22_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_9 k)) := by decide +kernel

theorem rowsSound22_9 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval11594 x
  · exact rowEval11595 x
  · exact rowEval11596 x
  · exact rowEval11597 x
  · exact rowEval11598 x
  · exact rowEval11599 x
  · exact rowEval11600 x
  · exact rowEval11601 x
  · exact rowEval11602 x
  · exact rowEval11603 x
  · exact rowEval11604 x
  · exact rowEval11605 x
  · exact rowEval11018 x
  · exact rowEval11019 x
  · exact rowEval11020 x
  · exact rowEval11021 x
  · exact rowEval11022 x
  · exact rowEval11023 x
  · exact rowEval11024 x
  · exact rowEval11025 x
  · exact rowEval11026 x
  · exact rowEval11027 x
  · exact rowEval11028 x
  · exact rowEval11029 x
  · exact rowEval11030 x
  · exact rowEval11031 x
  · exact rowEval11032 x
  · exact rowEval11033 x
  · exact rowEval11034 x
  · exact rowEval11035 x
  · exact rowEval11036 x
  · exact rowEval11037 x
  · exact rowEval11038 x
  · exact rowEval11039 x
  · exact rowEval11040 x
  · exact rowEval11041 x

theorem entryEval22_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_9 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck22_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_9]

def rows22_10 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11606, row11607, row11608, row11609, row11610, row11611, row11612, row11613, row11614, row11615, row11616, row11617, row11054, row11055, row11056, row11057, row11058, row11059, row11060, row11061, row11062, row11063, row11064, row11065, row11066, row11067, row11068, row11069, row11070, row11071, row11072, row11073, row11074, row11075, row11076, row11077]

theorem entryCheck22_10 : entry22_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_10 k)) := by decide +kernel

theorem rowsSound22_10 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval11606 x
  · exact rowEval11607 x
  · exact rowEval11608 x
  · exact rowEval11609 x
  · exact rowEval11610 x
  · exact rowEval11611 x
  · exact rowEval11612 x
  · exact rowEval11613 x
  · exact rowEval11614 x
  · exact rowEval11615 x
  · exact rowEval11616 x
  · exact rowEval11617 x
  · exact rowEval11054 x
  · exact rowEval11055 x
  · exact rowEval11056 x
  · exact rowEval11057 x
  · exact rowEval11058 x
  · exact rowEval11059 x
  · exact rowEval11060 x
  · exact rowEval11061 x
  · exact rowEval11062 x
  · exact rowEval11063 x
  · exact rowEval11064 x
  · exact rowEval11065 x
  · exact rowEval11066 x
  · exact rowEval11067 x
  · exact rowEval11068 x
  · exact rowEval11069 x
  · exact rowEval11070 x
  · exact rowEval11071 x
  · exact rowEval11072 x
  · exact rowEval11073 x
  · exact rowEval11074 x
  · exact rowEval11075 x
  · exact rowEval11076 x
  · exact rowEval11077 x

theorem entryEval22_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_10 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck22_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_10]

def rows22_11 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11618, row11619, row11620, row11621, row11622, row11623, row11624, row11625, row11626, row11627, row11628, row11629, row11090, row11091, row11092, row11093, row11094, row11095, row11096, row11097, row11098, row11099, row11100, row11101, row11102, row11103, row11104, row11105, row11106, row11107, row11108, row11109, row11110, row11111, row11112, row11113]

theorem entryCheck22_11 : entry22_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_11 k)) := by decide +kernel

theorem rowsSound22_11 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval11618 x
  · exact rowEval11619 x
  · exact rowEval11620 x
  · exact rowEval11621 x
  · exact rowEval11622 x
  · exact rowEval11623 x
  · exact rowEval11624 x
  · exact rowEval11625 x
  · exact rowEval11626 x
  · exact rowEval11627 x
  · exact rowEval11628 x
  · exact rowEval11629 x
  · exact rowEval11090 x
  · exact rowEval11091 x
  · exact rowEval11092 x
  · exact rowEval11093 x
  · exact rowEval11094 x
  · exact rowEval11095 x
  · exact rowEval11096 x
  · exact rowEval11097 x
  · exact rowEval11098 x
  · exact rowEval11099 x
  · exact rowEval11100 x
  · exact rowEval11101 x
  · exact rowEval11102 x
  · exact rowEval11103 x
  · exact rowEval11104 x
  · exact rowEval11105 x
  · exact rowEval11106 x
  · exact rowEval11107 x
  · exact rowEval11108 x
  · exact rowEval11109 x
  · exact rowEval11110 x
  · exact rowEval11111 x
  · exact rowEval11112 x
  · exact rowEval11113 x

theorem entryEval22_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_11 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck22_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_11]

def rows22_12 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11630, row11631, row11632, row11633, row11634, row11635, row11636, row11637, row11638, row11639, row11640, row11641, row11126, row11127, row11128, row11129, row11130, row11131, row11132, row11133, row11134, row11135, row11136, row11137, row11138, row11139, row11140, row11141, row11142, row11143, row11144, row11145, row11146, row11147, row11148, row11149]

theorem entryCheck22_12 : entry22_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_12 k)) := by decide +kernel

theorem rowsSound22_12 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval11630 x
  · exact rowEval11631 x
  · exact rowEval11632 x
  · exact rowEval11633 x
  · exact rowEval11634 x
  · exact rowEval11635 x
  · exact rowEval11636 x
  · exact rowEval11637 x
  · exact rowEval11638 x
  · exact rowEval11639 x
  · exact rowEval11640 x
  · exact rowEval11641 x
  · exact rowEval11126 x
  · exact rowEval11127 x
  · exact rowEval11128 x
  · exact rowEval11129 x
  · exact rowEval11130 x
  · exact rowEval11131 x
  · exact rowEval11132 x
  · exact rowEval11133 x
  · exact rowEval11134 x
  · exact rowEval11135 x
  · exact rowEval11136 x
  · exact rowEval11137 x
  · exact rowEval11138 x
  · exact rowEval11139 x
  · exact rowEval11140 x
  · exact rowEval11141 x
  · exact rowEval11142 x
  · exact rowEval11143 x
  · exact rowEval11144 x
  · exact rowEval11145 x
  · exact rowEval11146 x
  · exact rowEval11147 x
  · exact rowEval11148 x
  · exact rowEval11149 x

theorem entryEval22_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_12 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck22_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_12]

def rows22_13 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11642, row11643, row11644, row11645, row11646, row11647, row11648, row11649, row11650, row11651, row11652, row11653, row11162, row11163, row11164, row11165, row11166, row11167, row11168, row11169, row11170, row11171, row11172, row11173, row11174, row11175, row11176, row11177, row11178, row11179, row11180, row11181, row11182, row11183, row11184, row11185]

theorem entryCheck22_13 : entry22_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_13 k)) := by decide +kernel

theorem rowsSound22_13 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval11642 x
  · exact rowEval11643 x
  · exact rowEval11644 x
  · exact rowEval11645 x
  · exact rowEval11646 x
  · exact rowEval11647 x
  · exact rowEval11648 x
  · exact rowEval11649 x
  · exact rowEval11650 x
  · exact rowEval11651 x
  · exact rowEval11652 x
  · exact rowEval11653 x
  · exact rowEval11162 x
  · exact rowEval11163 x
  · exact rowEval11164 x
  · exact rowEval11165 x
  · exact rowEval11166 x
  · exact rowEval11167 x
  · exact rowEval11168 x
  · exact rowEval11169 x
  · exact rowEval11170 x
  · exact rowEval11171 x
  · exact rowEval11172 x
  · exact rowEval11173 x
  · exact rowEval11174 x
  · exact rowEval11175 x
  · exact rowEval11176 x
  · exact rowEval11177 x
  · exact rowEval11178 x
  · exact rowEval11179 x
  · exact rowEval11180 x
  · exact rowEval11181 x
  · exact rowEval11182 x
  · exact rowEval11183 x
  · exact rowEval11184 x
  · exact rowEval11185 x

theorem entryEval22_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_13 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck22_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_13]

def rows22_14 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11654, row11655, row11656, row11657, row11658, row11659, row11660, row11661, row11662, row11663, row11664, row11665, row11198, row11199, row11200, row11201, row11202, row11203, row11204, row11205, row11206, row11207, row11208, row11209, row11210, row11211, row11212, row11213, row11214, row11215, row11216, row11217, row11218, row11219, row11220, row11221]

theorem entryCheck22_14 : entry22_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_14 k)) := by decide +kernel

theorem rowsSound22_14 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval11654 x
  · exact rowEval11655 x
  · exact rowEval11656 x
  · exact rowEval11657 x
  · exact rowEval11658 x
  · exact rowEval11659 x
  · exact rowEval11660 x
  · exact rowEval11661 x
  · exact rowEval11662 x
  · exact rowEval11663 x
  · exact rowEval11664 x
  · exact rowEval11665 x
  · exact rowEval11198 x
  · exact rowEval11199 x
  · exact rowEval11200 x
  · exact rowEval11201 x
  · exact rowEval11202 x
  · exact rowEval11203 x
  · exact rowEval11204 x
  · exact rowEval11205 x
  · exact rowEval11206 x
  · exact rowEval11207 x
  · exact rowEval11208 x
  · exact rowEval11209 x
  · exact rowEval11210 x
  · exact rowEval11211 x
  · exact rowEval11212 x
  · exact rowEval11213 x
  · exact rowEval11214 x
  · exact rowEval11215 x
  · exact rowEval11216 x
  · exact rowEval11217 x
  · exact rowEval11218 x
  · exact rowEval11219 x
  · exact rowEval11220 x
  · exact rowEval11221 x

theorem entryEval22_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_14 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck22_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_14]

def rows22_15 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11666, row11667, row11668, row11669, row11670, row11671, row11672, row11673, row11674, row11675, row11676, row11677, row11234, row11235, row11236, row11237, row11238, row11239, row11240, row11241, row11242, row11243, row11244, row11245, row11246, row11247, row11248, row11249, row11250, row11251, row11252, row11253, row11254, row11255, row11256, row11257]

theorem entryCheck22_15 : entry22_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_15 k)) := by decide +kernel

theorem rowsSound22_15 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval11666 x
  · exact rowEval11667 x
  · exact rowEval11668 x
  · exact rowEval11669 x
  · exact rowEval11670 x
  · exact rowEval11671 x
  · exact rowEval11672 x
  · exact rowEval11673 x
  · exact rowEval11674 x
  · exact rowEval11675 x
  · exact rowEval11676 x
  · exact rowEval11677 x
  · exact rowEval11234 x
  · exact rowEval11235 x
  · exact rowEval11236 x
  · exact rowEval11237 x
  · exact rowEval11238 x
  · exact rowEval11239 x
  · exact rowEval11240 x
  · exact rowEval11241 x
  · exact rowEval11242 x
  · exact rowEval11243 x
  · exact rowEval11244 x
  · exact rowEval11245 x
  · exact rowEval11246 x
  · exact rowEval11247 x
  · exact rowEval11248 x
  · exact rowEval11249 x
  · exact rowEval11250 x
  · exact rowEval11251 x
  · exact rowEval11252 x
  · exact rowEval11253 x
  · exact rowEval11254 x
  · exact rowEval11255 x
  · exact rowEval11256 x
  · exact rowEval11257 x

theorem entryEval22_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_15 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck22_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_15]

def rows22_16 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11678, row11679, row11680, row11681, row11682, row11683, row11684, row11685, row11686, row11687, row11688, row11689, row11270, row11271, row11272, row11273, row11274, row11275, row11276, row11277, row11278, row11279, row11280, row11281, row11282, row11283, row11284, row11285, row11286, row11287, row11288, row11289, row11290, row11291, row11292, row11293]

theorem entryCheck22_16 : entry22_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_16 k)) := by decide +kernel

theorem rowsSound22_16 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval11678 x
  · exact rowEval11679 x
  · exact rowEval11680 x
  · exact rowEval11681 x
  · exact rowEval11682 x
  · exact rowEval11683 x
  · exact rowEval11684 x
  · exact rowEval11685 x
  · exact rowEval11686 x
  · exact rowEval11687 x
  · exact rowEval11688 x
  · exact rowEval11689 x
  · exact rowEval11270 x
  · exact rowEval11271 x
  · exact rowEval11272 x
  · exact rowEval11273 x
  · exact rowEval11274 x
  · exact rowEval11275 x
  · exact rowEval11276 x
  · exact rowEval11277 x
  · exact rowEval11278 x
  · exact rowEval11279 x
  · exact rowEval11280 x
  · exact rowEval11281 x
  · exact rowEval11282 x
  · exact rowEval11283 x
  · exact rowEval11284 x
  · exact rowEval11285 x
  · exact rowEval11286 x
  · exact rowEval11287 x
  · exact rowEval11288 x
  · exact rowEval11289 x
  · exact rowEval11290 x
  · exact rowEval11291 x
  · exact rowEval11292 x
  · exact rowEval11293 x

theorem entryEval22_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_16 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck22_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_16]

def rows22_17 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11690, row11691, row11692, row11693, row11694, row11695, row11696, row11697, row11698, row11699, row11700, row11701, row11306, row11307, row11308, row11309, row11310, row11311, row11312, row11313, row11314, row11315, row11316, row11317, row11318, row11319, row11320, row11321, row11322, row11323, row11324, row11325, row11326, row11327, row11328, row11329]

theorem entryCheck22_17 : entry22_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_17 k)) := by decide +kernel

theorem rowsSound22_17 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval11690 x
  · exact rowEval11691 x
  · exact rowEval11692 x
  · exact rowEval11693 x
  · exact rowEval11694 x
  · exact rowEval11695 x
  · exact rowEval11696 x
  · exact rowEval11697 x
  · exact rowEval11698 x
  · exact rowEval11699 x
  · exact rowEval11700 x
  · exact rowEval11701 x
  · exact rowEval11306 x
  · exact rowEval11307 x
  · exact rowEval11308 x
  · exact rowEval11309 x
  · exact rowEval11310 x
  · exact rowEval11311 x
  · exact rowEval11312 x
  · exact rowEval11313 x
  · exact rowEval11314 x
  · exact rowEval11315 x
  · exact rowEval11316 x
  · exact rowEval11317 x
  · exact rowEval11318 x
  · exact rowEval11319 x
  · exact rowEval11320 x
  · exact rowEval11321 x
  · exact rowEval11322 x
  · exact rowEval11323 x
  · exact rowEval11324 x
  · exact rowEval11325 x
  · exact rowEval11326 x
  · exact rowEval11327 x
  · exact rowEval11328 x
  · exact rowEval11329 x

theorem entryEval22_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_17 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck22_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_17]

def rows22_18 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11702, row11703, row11704, row11705, row11706, row11707, row11708, row11709, row11710, row11711, row11712, row11713, row11342, row11343, row11344, row11345, row11346, row11347, row11348, row11349, row11350, row11351, row11352, row11353, row11354, row11355, row11356, row11357, row11358, row11359, row11360, row11361, row11362, row11363, row11364, row11365]

theorem entryCheck22_18 : entry22_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_18 k)) := by decide +kernel

theorem rowsSound22_18 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval11702 x
  · exact rowEval11703 x
  · exact rowEval11704 x
  · exact rowEval11705 x
  · exact rowEval11706 x
  · exact rowEval11707 x
  · exact rowEval11708 x
  · exact rowEval11709 x
  · exact rowEval11710 x
  · exact rowEval11711 x
  · exact rowEval11712 x
  · exact rowEval11713 x
  · exact rowEval11342 x
  · exact rowEval11343 x
  · exact rowEval11344 x
  · exact rowEval11345 x
  · exact rowEval11346 x
  · exact rowEval11347 x
  · exact rowEval11348 x
  · exact rowEval11349 x
  · exact rowEval11350 x
  · exact rowEval11351 x
  · exact rowEval11352 x
  · exact rowEval11353 x
  · exact rowEval11354 x
  · exact rowEval11355 x
  · exact rowEval11356 x
  · exact rowEval11357 x
  · exact rowEval11358 x
  · exact rowEval11359 x
  · exact rowEval11360 x
  · exact rowEval11361 x
  · exact rowEval11362 x
  · exact rowEval11363 x
  · exact rowEval11364 x
  · exact rowEval11365 x

theorem entryEval22_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_18 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck22_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_18]

def rows22_19 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11714, row11715, row11716, row11717, row11718, row11719, row11720, row11721, row11722, row11723, row11724, row11725, row11378, row11379, row11380, row11381, row11382, row11383, row11384, row11385, row11386, row11387, row11388, row11389, row11390, row11391, row11392, row11393, row11394, row11395, row11396, row11397, row11398, row11399, row11400, row11401]

theorem entryCheck22_19 : entry22_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_19 k)) := by decide +kernel

theorem rowsSound22_19 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval11714 x
  · exact rowEval11715 x
  · exact rowEval11716 x
  · exact rowEval11717 x
  · exact rowEval11718 x
  · exact rowEval11719 x
  · exact rowEval11720 x
  · exact rowEval11721 x
  · exact rowEval11722 x
  · exact rowEval11723 x
  · exact rowEval11724 x
  · exact rowEval11725 x
  · exact rowEval11378 x
  · exact rowEval11379 x
  · exact rowEval11380 x
  · exact rowEval11381 x
  · exact rowEval11382 x
  · exact rowEval11383 x
  · exact rowEval11384 x
  · exact rowEval11385 x
  · exact rowEval11386 x
  · exact rowEval11387 x
  · exact rowEval11388 x
  · exact rowEval11389 x
  · exact rowEval11390 x
  · exact rowEval11391 x
  · exact rowEval11392 x
  · exact rowEval11393 x
  · exact rowEval11394 x
  · exact rowEval11395 x
  · exact rowEval11396 x
  · exact rowEval11397 x
  · exact rowEval11398 x
  · exact rowEval11399 x
  · exact rowEval11400 x
  · exact rowEval11401 x

theorem entryEval22_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_19 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck22_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_19]

def rows22_20 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11726, row11727, row11728, row11729, row11730, row11731, row11732, row11733, row11734, row11735, row11736, row11737, row11414, row11415, row11416, row11417, row11418, row11419, row11420, row11421, row11422, row11423, row11424, row11425, row11426, row11427, row11428, row11429, row11430, row11431, row11432, row11433, row11434, row11435, row11436, row11437]

theorem entryCheck22_20 : entry22_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_20 k)) := by decide +kernel

theorem rowsSound22_20 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval11726 x
  · exact rowEval11727 x
  · exact rowEval11728 x
  · exact rowEval11729 x
  · exact rowEval11730 x
  · exact rowEval11731 x
  · exact rowEval11732 x
  · exact rowEval11733 x
  · exact rowEval11734 x
  · exact rowEval11735 x
  · exact rowEval11736 x
  · exact rowEval11737 x
  · exact rowEval11414 x
  · exact rowEval11415 x
  · exact rowEval11416 x
  · exact rowEval11417 x
  · exact rowEval11418 x
  · exact rowEval11419 x
  · exact rowEval11420 x
  · exact rowEval11421 x
  · exact rowEval11422 x
  · exact rowEval11423 x
  · exact rowEval11424 x
  · exact rowEval11425 x
  · exact rowEval11426 x
  · exact rowEval11427 x
  · exact rowEval11428 x
  · exact rowEval11429 x
  · exact rowEval11430 x
  · exact rowEval11431 x
  · exact rowEval11432 x
  · exact rowEval11433 x
  · exact rowEval11434 x
  · exact rowEval11435 x
  · exact rowEval11436 x
  · exact rowEval11437 x

theorem entryEval22_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_20 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck22_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_20]

def rows22_21 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11738, row11739, row11740, row11741, row11742, row11743, row11744, row11745, row11746, row11747, row11748, row11749, row11450, row11451, row11452, row11453, row11454, row11455, row11456, row11457, row11458, row11459, row11460, row11461, row11462, row11463, row11464, row11465, row11466, row11467, row11468, row11469, row11470, row11471, row11472, row11473]

theorem entryCheck22_21 : entry22_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_21 k)) := by decide +kernel

theorem rowsSound22_21 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
  · exact rowEval11738 x
  · exact rowEval11739 x
  · exact rowEval11740 x
  · exact rowEval11741 x
  · exact rowEval11742 x
  · exact rowEval11743 x
  · exact rowEval11744 x
  · exact rowEval11745 x
  · exact rowEval11746 x
  · exact rowEval11747 x
  · exact rowEval11748 x
  · exact rowEval11749 x
  · exact rowEval11450 x
  · exact rowEval11451 x
  · exact rowEval11452 x
  · exact rowEval11453 x
  · exact rowEval11454 x
  · exact rowEval11455 x
  · exact rowEval11456 x
  · exact rowEval11457 x
  · exact rowEval11458 x
  · exact rowEval11459 x
  · exact rowEval11460 x
  · exact rowEval11461 x
  · exact rowEval11462 x
  · exact rowEval11463 x
  · exact rowEval11464 x
  · exact rowEval11465 x
  · exact rowEval11466 x
  · exact rowEval11467 x
  · exact rowEval11468 x
  · exact rowEval11469 x
  · exact rowEval11470 x
  · exact rowEval11471 x
  · exact rowEval11472 x
  · exact rowEval11473 x

theorem entryEval22_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_21 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck22_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_21]

def rows22_22 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11750, row11751, row11752, row11753, row11754, row11755, row11756, row11757, row11758, row11759, row11760, row11761, row11762, row11763, row11764, row11765, row11766, row11767, row11768, row11769, row11770, row11771, row11772, row11773, row11774, row11775, row11776, row11777, row11778, row11779, row11780, row11781, row11782, row11783, row11784, row11785]

theorem entryCheck22_22 : entry22_22 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_22 k)) := by decide +kernel

theorem rowsSound22_22 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_22 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form22) x := by
  fin_cases k
  · exact rowEval11750 x
  · exact rowEval11751 x
  · exact rowEval11752 x
  · exact rowEval11753 x
  · exact rowEval11754 x
  · exact rowEval11755 x
  · exact rowEval11756 x
  · exact rowEval11757 x
  · exact rowEval11758 x
  · exact rowEval11759 x
  · exact rowEval11760 x
  · exact rowEval11761 x
  · exact rowEval11762 x
  · exact rowEval11763 x
  · exact rowEval11764 x
  · exact rowEval11765 x
  · exact rowEval11766 x
  · exact rowEval11767 x
  · exact rowEval11768 x
  · exact rowEval11769 x
  · exact rowEval11770 x
  · exact rowEval11771 x
  · exact rowEval11772 x
  · exact rowEval11773 x
  · exact rowEval11774 x
  · exact rowEval11775 x
  · exact rowEval11776 x
  · exact rowEval11777 x
  · exact rowEval11778 x
  · exact rowEval11779 x
  · exact rowEval11780 x
  · exact rowEval11781 x
  · exact rowEval11782 x
  · exact rowEval11783 x
  · exact rowEval11784 x
  · exact rowEval11785 x

theorem entryEval22_22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_22 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form22 B := by
  rw [entryCheck22_22, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form22 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_22]

end MUB6.Certificate.GramEntries.Block3

end OAI
