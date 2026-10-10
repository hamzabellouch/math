import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block107
import OAI.Analysis.MutuallyUnbiased.GramRows.Block108
import OAI.Analysis.MutuallyUnbiased.GramRows.Block109
import OAI.Analysis.MutuallyUnbiased.GramRows.Block110
import OAI.Analysis.MutuallyUnbiased.GramRows.Block111
import OAI.Analysis.MutuallyUnbiased.GramRows.Block112
import OAI.Analysis.MutuallyUnbiased.GramRows.Block113

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows21_0 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10694, row10695, row10696, row10697, row10698, row10699, row10700, row10701, row10702, row10703, row10704, row10705, row10706, row10707, row10708, row10709, row10710, row10711, row10712, row10713, row10714, row10715, row10716, row10717, row10718, row10719, row10720, row10721, row10722, row10723, row10724, row10725, row10726, row10727, row10728, row10729]

theorem entryCheck21_0 : entry21_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_0 k)) := by decide +kernel

theorem rowsSound21_0 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
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
  · exact rowEval10718 x
  · exact rowEval10719 x
  · exact rowEval10720 x
  · exact rowEval10721 x
  · exact rowEval10722 x
  · exact rowEval10723 x
  · exact rowEval10724 x
  · exact rowEval10725 x
  · exact rowEval10726 x
  · exact rowEval10727 x
  · exact rowEval10728 x
  · exact rowEval10729 x

theorem entryEval21_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_0 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck21_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_0]

def rows21_1 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10730, row10731, row10732, row10733, row10734, row10735, row10736, row10737, row10738, row10739, row10740, row10741, row10742, row10743, row10744, row10745, row10746, row10747, row10748, row10749, row10750, row10751, row10752, row10753, row10754, row10755, row10756, row10757, row10758, row10759, row10760, row10761, row10762, row10763, row10764, row10765]

theorem entryCheck21_1 : entry21_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_1 k)) := by decide +kernel

theorem rowsSound21_1 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
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
  · exact rowEval10754 x
  · exact rowEval10755 x
  · exact rowEval10756 x
  · exact rowEval10757 x
  · exact rowEval10758 x
  · exact rowEval10759 x
  · exact rowEval10760 x
  · exact rowEval10761 x
  · exact rowEval10762 x
  · exact rowEval10763 x
  · exact rowEval10764 x
  · exact rowEval10765 x

theorem entryEval21_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_1 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck21_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_1]

def rows21_2 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10766, row10767, row10768, row10769, row10770, row10771, row10772, row10773, row10774, row10775, row10776, row10777, row10778, row10779, row10780, row10781, row10782, row10783, row10784, row10785, row10786, row10787, row10788, row10789, row10790, row10791, row10792, row10793, row10794, row10795, row10796, row10797, row10798, row10799, row10800, row10801]

theorem entryCheck21_2 : entry21_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_2 k)) := by decide +kernel

theorem rowsSound21_2 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
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
  · exact rowEval10790 x
  · exact rowEval10791 x
  · exact rowEval10792 x
  · exact rowEval10793 x
  · exact rowEval10794 x
  · exact rowEval10795 x
  · exact rowEval10796 x
  · exact rowEval10797 x
  · exact rowEval10798 x
  · exact rowEval10799 x
  · exact rowEval10800 x
  · exact rowEval10801 x

theorem entryEval21_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_2 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck21_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_2]

def rows21_3 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10802, row10803, row10804, row10805, row10806, row10807, row10808, row10809, row10810, row10811, row10812, row10813, row10814, row10815, row10816, row10817, row10818, row10819, row10820, row10821, row10822, row10823, row10824, row10825, row10826, row10827, row10828, row10829, row10830, row10831, row10832, row10833, row10834, row10835, row10836, row10837]

theorem entryCheck21_3 : entry21_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_3 k)) := by decide +kernel

theorem rowsSound21_3 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
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
  · exact rowEval10826 x
  · exact rowEval10827 x
  · exact rowEval10828 x
  · exact rowEval10829 x
  · exact rowEval10830 x
  · exact rowEval10831 x
  · exact rowEval10832 x
  · exact rowEval10833 x
  · exact rowEval10834 x
  · exact rowEval10835 x
  · exact rowEval10836 x
  · exact rowEval10837 x

theorem entryEval21_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_3 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck21_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_3]

def rows21_4 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10838, row10839, row10840, row10841, row10842, row10843, row10844, row10845, row10846, row10847, row10848, row10849, row10850, row10851, row10852, row10853, row10854, row10855, row10856, row10857, row10858, row10859, row10860, row10861, row10862, row10863, row10864, row10865, row10866, row10867, row10868, row10869, row10870, row10871, row10872, row10873]

theorem entryCheck21_4 : entry21_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_4 k)) := by decide +kernel

theorem rowsSound21_4 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
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
  · exact rowEval10862 x
  · exact rowEval10863 x
  · exact rowEval10864 x
  · exact rowEval10865 x
  · exact rowEval10866 x
  · exact rowEval10867 x
  · exact rowEval10868 x
  · exact rowEval10869 x
  · exact rowEval10870 x
  · exact rowEval10871 x
  · exact rowEval10872 x
  · exact rowEval10873 x

theorem entryEval21_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_4 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck21_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_4]

def rows21_5 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10874, row10875, row10876, row10877, row10878, row10879, row10880, row10881, row10882, row10883, row10884, row10885, row10886, row10887, row10888, row10889, row10890, row10891, row10892, row10893, row10894, row10895, row10896, row10897, row10898, row10899, row10900, row10901, row10902, row10903, row10904, row10905, row10906, row10907, row10908, row10909]

theorem entryCheck21_5 : entry21_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_5 k)) := by decide +kernel

theorem rowsSound21_5 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
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
  · exact rowEval10898 x
  · exact rowEval10899 x
  · exact rowEval10900 x
  · exact rowEval10901 x
  · exact rowEval10902 x
  · exact rowEval10903 x
  · exact rowEval10904 x
  · exact rowEval10905 x
  · exact rowEval10906 x
  · exact rowEval10907 x
  · exact rowEval10908 x
  · exact rowEval10909 x

theorem entryEval21_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_5 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck21_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_5]

def rows21_6 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10910, row10911, row10912, row10913, row10914, row10915, row10916, row10917, row10918, row10919, row10920, row10921, row10922, row10923, row10924, row10925, row10926, row10927, row10928, row10929, row10930, row10931, row10932, row10933, row10934, row10935, row10936, row10937, row10938, row10939, row10940, row10941, row10942, row10943, row10944, row10945]

theorem entryCheck21_6 : entry21_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_6 k)) := by decide +kernel

theorem rowsSound21_6 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
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
  · exact rowEval10934 x
  · exact rowEval10935 x
  · exact rowEval10936 x
  · exact rowEval10937 x
  · exact rowEval10938 x
  · exact rowEval10939 x
  · exact rowEval10940 x
  · exact rowEval10941 x
  · exact rowEval10942 x
  · exact rowEval10943 x
  · exact rowEval10944 x
  · exact rowEval10945 x

theorem entryEval21_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_6 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck21_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_6]

def rows21_7 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10946, row10947, row10948, row10949, row10950, row10951, row10952, row10953, row10954, row10955, row10956, row10957, row10958, row10959, row10960, row10961, row10962, row10963, row10964, row10965, row10966, row10967, row10968, row10969, row10970, row10971, row10972, row10973, row10974, row10975, row10976, row10977, row10978, row10979, row10980, row10981]

theorem entryCheck21_7 : entry21_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_7 k)) := by decide +kernel

theorem rowsSound21_7 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
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
  · exact rowEval10970 x
  · exact rowEval10971 x
  · exact rowEval10972 x
  · exact rowEval10973 x
  · exact rowEval10974 x
  · exact rowEval10975 x
  · exact rowEval10976 x
  · exact rowEval10977 x
  · exact rowEval10978 x
  · exact rowEval10979 x
  · exact rowEval10980 x
  · exact rowEval10981 x

theorem entryEval21_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_7 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck21_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_7]

def rows21_8 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10982, row10983, row10984, row10985, row10986, row10987, row10988, row10989, row10990, row10991, row10992, row10993, row10994, row10995, row10996, row10997, row10998, row10999, row11000, row11001, row11002, row11003, row11004, row11005, row11006, row11007, row11008, row11009, row11010, row11011, row11012, row11013, row11014, row11015, row11016, row11017]

theorem entryCheck21_8 : entry21_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_8 k)) := by decide +kernel

theorem rowsSound21_8 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
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
  · exact rowEval11006 x
  · exact rowEval11007 x
  · exact rowEval11008 x
  · exact rowEval11009 x
  · exact rowEval11010 x
  · exact rowEval11011 x
  · exact rowEval11012 x
  · exact rowEval11013 x
  · exact rowEval11014 x
  · exact rowEval11015 x
  · exact rowEval11016 x
  · exact rowEval11017 x

theorem entryEval21_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_8 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck21_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_8]

def rows21_9 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11018, row11019, row11020, row11021, row11022, row11023, row11024, row11025, row11026, row11027, row11028, row11029, row11030, row11031, row11032, row11033, row11034, row11035, row11036, row11037, row11038, row11039, row11040, row11041, row11042, row11043, row11044, row11045, row11046, row11047, row11048, row11049, row11050, row11051, row11052, row11053]

theorem entryCheck21_9 : entry21_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_9 k)) := by decide +kernel

theorem rowsSound21_9 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
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
  · exact rowEval11042 x
  · exact rowEval11043 x
  · exact rowEval11044 x
  · exact rowEval11045 x
  · exact rowEval11046 x
  · exact rowEval11047 x
  · exact rowEval11048 x
  · exact rowEval11049 x
  · exact rowEval11050 x
  · exact rowEval11051 x
  · exact rowEval11052 x
  · exact rowEval11053 x

theorem entryEval21_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_9 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck21_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_9]

def rows21_10 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11054, row11055, row11056, row11057, row11058, row11059, row11060, row11061, row11062, row11063, row11064, row11065, row11066, row11067, row11068, row11069, row11070, row11071, row11072, row11073, row11074, row11075, row11076, row11077, row11078, row11079, row11080, row11081, row11082, row11083, row11084, row11085, row11086, row11087, row11088, row11089]

theorem entryCheck21_10 : entry21_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_10 k)) := by decide +kernel

theorem rowsSound21_10 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
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
  · exact rowEval11078 x
  · exact rowEval11079 x
  · exact rowEval11080 x
  · exact rowEval11081 x
  · exact rowEval11082 x
  · exact rowEval11083 x
  · exact rowEval11084 x
  · exact rowEval11085 x
  · exact rowEval11086 x
  · exact rowEval11087 x
  · exact rowEval11088 x
  · exact rowEval11089 x

theorem entryEval21_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_10 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck21_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_10]

def rows21_11 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11090, row11091, row11092, row11093, row11094, row11095, row11096, row11097, row11098, row11099, row11100, row11101, row11102, row11103, row11104, row11105, row11106, row11107, row11108, row11109, row11110, row11111, row11112, row11113, row11114, row11115, row11116, row11117, row11118, row11119, row11120, row11121, row11122, row11123, row11124, row11125]

theorem entryCheck21_11 : entry21_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_11 k)) := by decide +kernel

theorem rowsSound21_11 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
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
  · exact rowEval11114 x
  · exact rowEval11115 x
  · exact rowEval11116 x
  · exact rowEval11117 x
  · exact rowEval11118 x
  · exact rowEval11119 x
  · exact rowEval11120 x
  · exact rowEval11121 x
  · exact rowEval11122 x
  · exact rowEval11123 x
  · exact rowEval11124 x
  · exact rowEval11125 x

theorem entryEval21_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_11 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck21_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_11]

def rows21_12 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11126, row11127, row11128, row11129, row11130, row11131, row11132, row11133, row11134, row11135, row11136, row11137, row11138, row11139, row11140, row11141, row11142, row11143, row11144, row11145, row11146, row11147, row11148, row11149, row11150, row11151, row11152, row11153, row11154, row11155, row11156, row11157, row11158, row11159, row11160, row11161]

theorem entryCheck21_12 : entry21_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_12 k)) := by decide +kernel

theorem rowsSound21_12 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
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
  · exact rowEval11150 x
  · exact rowEval11151 x
  · exact rowEval11152 x
  · exact rowEval11153 x
  · exact rowEval11154 x
  · exact rowEval11155 x
  · exact rowEval11156 x
  · exact rowEval11157 x
  · exact rowEval11158 x
  · exact rowEval11159 x
  · exact rowEval11160 x
  · exact rowEval11161 x

theorem entryEval21_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_12 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck21_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_12]

def rows21_13 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11162, row11163, row11164, row11165, row11166, row11167, row11168, row11169, row11170, row11171, row11172, row11173, row11174, row11175, row11176, row11177, row11178, row11179, row11180, row11181, row11182, row11183, row11184, row11185, row11186, row11187, row11188, row11189, row11190, row11191, row11192, row11193, row11194, row11195, row11196, row11197]

theorem entryCheck21_13 : entry21_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_13 k)) := by decide +kernel

theorem rowsSound21_13 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
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
  · exact rowEval11186 x
  · exact rowEval11187 x
  · exact rowEval11188 x
  · exact rowEval11189 x
  · exact rowEval11190 x
  · exact rowEval11191 x
  · exact rowEval11192 x
  · exact rowEval11193 x
  · exact rowEval11194 x
  · exact rowEval11195 x
  · exact rowEval11196 x
  · exact rowEval11197 x

theorem entryEval21_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_13 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck21_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_13]

def rows21_14 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11198, row11199, row11200, row11201, row11202, row11203, row11204, row11205, row11206, row11207, row11208, row11209, row11210, row11211, row11212, row11213, row11214, row11215, row11216, row11217, row11218, row11219, row11220, row11221, row11222, row11223, row11224, row11225, row11226, row11227, row11228, row11229, row11230, row11231, row11232, row11233]

theorem entryCheck21_14 : entry21_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_14 k)) := by decide +kernel

theorem rowsSound21_14 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
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
  · exact rowEval11222 x
  · exact rowEval11223 x
  · exact rowEval11224 x
  · exact rowEval11225 x
  · exact rowEval11226 x
  · exact rowEval11227 x
  · exact rowEval11228 x
  · exact rowEval11229 x
  · exact rowEval11230 x
  · exact rowEval11231 x
  · exact rowEval11232 x
  · exact rowEval11233 x

theorem entryEval21_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_14 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck21_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_14]

def rows21_15 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11234, row11235, row11236, row11237, row11238, row11239, row11240, row11241, row11242, row11243, row11244, row11245, row11246, row11247, row11248, row11249, row11250, row11251, row11252, row11253, row11254, row11255, row11256, row11257, row11258, row11259, row11260, row11261, row11262, row11263, row11264, row11265, row11266, row11267, row11268, row11269]

theorem entryCheck21_15 : entry21_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_15 k)) := by decide +kernel

theorem rowsSound21_15 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
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
  · exact rowEval11258 x
  · exact rowEval11259 x
  · exact rowEval11260 x
  · exact rowEval11261 x
  · exact rowEval11262 x
  · exact rowEval11263 x
  · exact rowEval11264 x
  · exact rowEval11265 x
  · exact rowEval11266 x
  · exact rowEval11267 x
  · exact rowEval11268 x
  · exact rowEval11269 x

theorem entryEval21_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_15 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck21_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_15]

def rows21_16 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11270, row11271, row11272, row11273, row11274, row11275, row11276, row11277, row11278, row11279, row11280, row11281, row11282, row11283, row11284, row11285, row11286, row11287, row11288, row11289, row11290, row11291, row11292, row11293, row11294, row11295, row11296, row11297, row11298, row11299, row11300, row11301, row11302, row11303, row11304, row11305]

theorem entryCheck21_16 : entry21_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_16 k)) := by decide +kernel

theorem rowsSound21_16 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
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
  · exact rowEval11294 x
  · exact rowEval11295 x
  · exact rowEval11296 x
  · exact rowEval11297 x
  · exact rowEval11298 x
  · exact rowEval11299 x
  · exact rowEval11300 x
  · exact rowEval11301 x
  · exact rowEval11302 x
  · exact rowEval11303 x
  · exact rowEval11304 x
  · exact rowEval11305 x

theorem entryEval21_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_16 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck21_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_16]

def rows21_17 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11306, row11307, row11308, row11309, row11310, row11311, row11312, row11313, row11314, row11315, row11316, row11317, row11318, row11319, row11320, row11321, row11322, row11323, row11324, row11325, row11326, row11327, row11328, row11329, row11330, row11331, row11332, row11333, row11334, row11335, row11336, row11337, row11338, row11339, row11340, row11341]

theorem entryCheck21_17 : entry21_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_17 k)) := by decide +kernel

theorem rowsSound21_17 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
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
  · exact rowEval11330 x
  · exact rowEval11331 x
  · exact rowEval11332 x
  · exact rowEval11333 x
  · exact rowEval11334 x
  · exact rowEval11335 x
  · exact rowEval11336 x
  · exact rowEval11337 x
  · exact rowEval11338 x
  · exact rowEval11339 x
  · exact rowEval11340 x
  · exact rowEval11341 x

theorem entryEval21_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_17 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck21_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_17]

def rows21_18 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11342, row11343, row11344, row11345, row11346, row11347, row11348, row11349, row11350, row11351, row11352, row11353, row11354, row11355, row11356, row11357, row11358, row11359, row11360, row11361, row11362, row11363, row11364, row11365, row11366, row11367, row11368, row11369, row11370, row11371, row11372, row11373, row11374, row11375, row11376, row11377]

theorem entryCheck21_18 : entry21_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_18 k)) := by decide +kernel

theorem rowsSound21_18 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
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
  · exact rowEval11366 x
  · exact rowEval11367 x
  · exact rowEval11368 x
  · exact rowEval11369 x
  · exact rowEval11370 x
  · exact rowEval11371 x
  · exact rowEval11372 x
  · exact rowEval11373 x
  · exact rowEval11374 x
  · exact rowEval11375 x
  · exact rowEval11376 x
  · exact rowEval11377 x

theorem entryEval21_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_18 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck21_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_18]

def rows21_19 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11378, row11379, row11380, row11381, row11382, row11383, row11384, row11385, row11386, row11387, row11388, row11389, row11390, row11391, row11392, row11393, row11394, row11395, row11396, row11397, row11398, row11399, row11400, row11401, row11402, row11403, row11404, row11405, row11406, row11407, row11408, row11409, row11410, row11411, row11412, row11413]

theorem entryCheck21_19 : entry21_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_19 k)) := by decide +kernel

theorem rowsSound21_19 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
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
  · exact rowEval11402 x
  · exact rowEval11403 x
  · exact rowEval11404 x
  · exact rowEval11405 x
  · exact rowEval11406 x
  · exact rowEval11407 x
  · exact rowEval11408 x
  · exact rowEval11409 x
  · exact rowEval11410 x
  · exact rowEval11411 x
  · exact rowEval11412 x
  · exact rowEval11413 x

theorem entryEval21_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_19 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck21_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_19]

def rows21_20 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11414, row11415, row11416, row11417, row11418, row11419, row11420, row11421, row11422, row11423, row11424, row11425, row11426, row11427, row11428, row11429, row11430, row11431, row11432, row11433, row11434, row11435, row11436, row11437, row11438, row11439, row11440, row11441, row11442, row11443, row11444, row11445, row11446, row11447, row11448, row11449]

theorem entryCheck21_20 : entry21_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_20 k)) := by decide +kernel

theorem rowsSound21_20 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
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
  · exact rowEval11438 x
  · exact rowEval11439 x
  · exact rowEval11440 x
  · exact rowEval11441 x
  · exact rowEval11442 x
  · exact rowEval11443 x
  · exact rowEval11444 x
  · exact rowEval11445 x
  · exact rowEval11446 x
  · exact rowEval11447 x
  · exact rowEval11448 x
  · exact rowEval11449 x

theorem entryEval21_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_20 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck21_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_20]

def rows21_21 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11450, row11451, row11452, row11453, row11454, row11455, row11456, row11457, row11458, row11459, row11460, row11461, row11462, row11463, row11464, row11465, row11466, row11467, row11468, row11469, row11470, row11471, row11472, row11473, row11474, row11475, row11476, row11477, row11478, row11479, row11480, row11481, row11482, row11483, row11484, row11485]

theorem entryCheck21_21 : entry21_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_21 k)) := by decide +kernel

theorem rowsSound21_21 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
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
  · exact rowEval11474 x
  · exact rowEval11475 x
  · exact rowEval11476 x
  · exact rowEval11477 x
  · exact rowEval11478 x
  · exact rowEval11479 x
  · exact rowEval11480 x
  · exact rowEval11481 x
  · exact rowEval11482 x
  · exact rowEval11483 x
  · exact rowEval11484 x
  · exact rowEval11485 x

theorem entryEval21_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_21 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck21_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_21]

end MUB6.Certificate.GramEntries.Block3

end OAI
