import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block16
import OAI.Analysis.MutuallyUnbiased.GramRows.Block17
import OAI.Analysis.MutuallyUnbiased.GramRows.Block35
import OAI.Analysis.MutuallyUnbiased.GramRows.Block36
import OAI.Analysis.MutuallyUnbiased.GramRows.Block37
import OAI.Analysis.MutuallyUnbiased.GramRows.Block61
import OAI.Analysis.MutuallyUnbiased.GramRows.Block62
import OAI.Analysis.MutuallyUnbiased.GramRows.Block63
import OAI.Analysis.MutuallyUnbiased.GramRows.Block64

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows20_0 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4836, row4837, row4838, row1476, row1477, row1478, row4839, row4840, row4841, row630, row631, row632, row1485, row1486, row1487, row639, row640, row641]

theorem entryCheck20_0 : entry20_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_0 k)) := by decide +kernel

theorem rowsSound20_0 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval4836 x
  · exact rowEval4837 x
  · exact rowEval4838 x
  · exact rowEval1476 x
  · exact rowEval1477 x
  · exact rowEval1478 x
  · exact rowEval4839 x
  · exact rowEval4840 x
  · exact rowEval4841 x
  · exact rowEval630 x
  · exact rowEval631 x
  · exact rowEval632 x
  · exact rowEval1485 x
  · exact rowEval1486 x
  · exact rowEval1487 x
  · exact rowEval639 x
  · exact rowEval640 x
  · exact rowEval641 x

theorem entryEval20_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_0 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck20_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_0]

def rows20_1 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4842, row4843, row4844, row1494, row1495, row1496, row4845, row4846, row4847, row4848, row4849, row4850, row1503, row1504, row1505, row4851, row4852, row4853]

theorem entryCheck20_1 : entry20_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_1 k)) := by decide +kernel

theorem rowsSound20_1 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval4842 x
  · exact rowEval4843 x
  · exact rowEval4844 x
  · exact rowEval1494 x
  · exact rowEval1495 x
  · exact rowEval1496 x
  · exact rowEval4845 x
  · exact rowEval4846 x
  · exact rowEval4847 x
  · exact rowEval4848 x
  · exact rowEval4849 x
  · exact rowEval4850 x
  · exact rowEval1503 x
  · exact rowEval1504 x
  · exact rowEval1505 x
  · exact rowEval4851 x
  · exact rowEval4852 x
  · exact rowEval4853 x

theorem entryEval20_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_1 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck20_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_1]

def rows20_2 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4854, row4855, row4856, row1524, row1525, row1526, row4857, row4858, row4859, row4860, row4861, row4862, row1533, row1534, row1535, row4863, row4864, row4865]

theorem entryCheck20_2 : entry20_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_2 k)) := by decide +kernel

theorem rowsSound20_2 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval4854 x
  · exact rowEval4855 x
  · exact rowEval4856 x
  · exact rowEval1524 x
  · exact rowEval1525 x
  · exact rowEval1526 x
  · exact rowEval4857 x
  · exact rowEval4858 x
  · exact rowEval4859 x
  · exact rowEval4860 x
  · exact rowEval4861 x
  · exact rowEval4862 x
  · exact rowEval1533 x
  · exact rowEval1534 x
  · exact rowEval1535 x
  · exact rowEval4863 x
  · exact rowEval4864 x
  · exact rowEval4865 x

theorem entryEval20_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_2 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck20_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_2]

def rows20_3 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4866, row4867, row4868, row1554, row1555, row1556, row4869, row4870, row4871, row4872, row4873, row4874, row1563, row1564, row1565, row4875, row4876, row4877]

theorem entryCheck20_3 : entry20_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_3 k)) := by decide +kernel

theorem rowsSound20_3 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval4866 x
  · exact rowEval4867 x
  · exact rowEval4868 x
  · exact rowEval1554 x
  · exact rowEval1555 x
  · exact rowEval1556 x
  · exact rowEval4869 x
  · exact rowEval4870 x
  · exact rowEval4871 x
  · exact rowEval4872 x
  · exact rowEval4873 x
  · exact rowEval4874 x
  · exact rowEval1563 x
  · exact rowEval1564 x
  · exact rowEval1565 x
  · exact rowEval4875 x
  · exact rowEval4876 x
  · exact rowEval4877 x

theorem entryEval20_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_3 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck20_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_3]

def rows20_4 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4878, row4879, row4880, row1584, row1585, row1586, row4881, row4882, row4883, row4884, row4885, row4886, row1593, row1594, row1595, row4887, row4888, row4889]

theorem entryCheck20_4 : entry20_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_4 k)) := by decide +kernel

theorem rowsSound20_4 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval4878 x
  · exact rowEval4879 x
  · exact rowEval4880 x
  · exact rowEval1584 x
  · exact rowEval1585 x
  · exact rowEval1586 x
  · exact rowEval4881 x
  · exact rowEval4882 x
  · exact rowEval4883 x
  · exact rowEval4884 x
  · exact rowEval4885 x
  · exact rowEval4886 x
  · exact rowEval1593 x
  · exact rowEval1594 x
  · exact rowEval1595 x
  · exact rowEval4887 x
  · exact rowEval4888 x
  · exact rowEval4889 x

theorem entryEval20_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_4 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck20_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_4]

def rows20_5 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4890, row4891, row4892, row1614, row1615, row1616, row4893, row4894, row4895, row4896, row4897, row4898, row1623, row1624, row1625, row4899, row4900, row4901]

theorem entryCheck20_5 : entry20_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_5 k)) := by decide +kernel

theorem rowsSound20_5 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval4890 x
  · exact rowEval4891 x
  · exact rowEval4892 x
  · exact rowEval1614 x
  · exact rowEval1615 x
  · exact rowEval1616 x
  · exact rowEval4893 x
  · exact rowEval4894 x
  · exact rowEval4895 x
  · exact rowEval4896 x
  · exact rowEval4897 x
  · exact rowEval4898 x
  · exact rowEval1623 x
  · exact rowEval1624 x
  · exact rowEval1625 x
  · exact rowEval4899 x
  · exact rowEval4900 x
  · exact rowEval4901 x

theorem entryEval20_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_5 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck20_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_5]

def rows20_6 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4902, row4903, row4904, row1644, row1645, row1646, row4905, row4906, row4907, row4908, row4909, row4910, row1653, row1654, row1655, row4911, row4912, row4913]

theorem entryCheck20_6 : entry20_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_6 k)) := by decide +kernel

theorem rowsSound20_6 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval4902 x
  · exact rowEval4903 x
  · exact rowEval4904 x
  · exact rowEval1644 x
  · exact rowEval1645 x
  · exact rowEval1646 x
  · exact rowEval4905 x
  · exact rowEval4906 x
  · exact rowEval4907 x
  · exact rowEval4908 x
  · exact rowEval4909 x
  · exact rowEval4910 x
  · exact rowEval1653 x
  · exact rowEval1654 x
  · exact rowEval1655 x
  · exact rowEval4911 x
  · exact rowEval4912 x
  · exact rowEval4913 x

theorem entryEval20_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_6 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck20_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_6]

def rows20_7 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4914, row4915, row4916, row1674, row1675, row1676, row4917, row4918, row4919, row4920, row4921, row4922, row1683, row1684, row1685, row4923, row4924, row4925]

theorem entryCheck20_7 : entry20_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_7 k)) := by decide +kernel

theorem rowsSound20_7 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval4914 x
  · exact rowEval4915 x
  · exact rowEval4916 x
  · exact rowEval1674 x
  · exact rowEval1675 x
  · exact rowEval1676 x
  · exact rowEval4917 x
  · exact rowEval4918 x
  · exact rowEval4919 x
  · exact rowEval4920 x
  · exact rowEval4921 x
  · exact rowEval4922 x
  · exact rowEval1683 x
  · exact rowEval1684 x
  · exact rowEval1685 x
  · exact rowEval4923 x
  · exact rowEval4924 x
  · exact rowEval4925 x

theorem entryEval20_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_7 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck20_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_7]

def rows20_8 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4926, row4927, row4928, row1704, row1705, row1706, row4929, row4930, row4931, row4932, row4933, row4934, row1713, row1714, row1715, row4935, row4936, row4937]

theorem entryCheck20_8 : entry20_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_8 k)) := by decide +kernel

theorem rowsSound20_8 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval4926 x
  · exact rowEval4927 x
  · exact rowEval4928 x
  · exact rowEval1704 x
  · exact rowEval1705 x
  · exact rowEval1706 x
  · exact rowEval4929 x
  · exact rowEval4930 x
  · exact rowEval4931 x
  · exact rowEval4932 x
  · exact rowEval4933 x
  · exact rowEval4934 x
  · exact rowEval1713 x
  · exact rowEval1714 x
  · exact rowEval1715 x
  · exact rowEval4935 x
  · exact rowEval4936 x
  · exact rowEval4937 x

theorem entryEval20_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_8 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck20_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_8]

def rows20_9 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4938, row4939, row4940, row1734, row1735, row1736, row4941, row4942, row4943, row4944, row4945, row4946, row1743, row1744, row1745, row4947, row4948, row4949]

theorem entryCheck20_9 : entry20_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_9 k)) := by decide +kernel

theorem rowsSound20_9 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval4938 x
  · exact rowEval4939 x
  · exact rowEval4940 x
  · exact rowEval1734 x
  · exact rowEval1735 x
  · exact rowEval1736 x
  · exact rowEval4941 x
  · exact rowEval4942 x
  · exact rowEval4943 x
  · exact rowEval4944 x
  · exact rowEval4945 x
  · exact rowEval4946 x
  · exact rowEval1743 x
  · exact rowEval1744 x
  · exact rowEval1745 x
  · exact rowEval4947 x
  · exact rowEval4948 x
  · exact rowEval4949 x

theorem entryEval20_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_9 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck20_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_9]

def rows20_10 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4950, row4951, row4952, row4953, row4954, row4955, row4956, row4957, row4958, row4959, row4960, row4961, row4962, row4963, row4964, row4965, row4966, row4967]

theorem entryCheck20_10 : entry20_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_10 k)) := by decide +kernel

theorem rowsSound20_10 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval4950 x
  · exact rowEval4951 x
  · exact rowEval4952 x
  · exact rowEval4953 x
  · exact rowEval4954 x
  · exact rowEval4955 x
  · exact rowEval4956 x
  · exact rowEval4957 x
  · exact rowEval4958 x
  · exact rowEval4959 x
  · exact rowEval4960 x
  · exact rowEval4961 x
  · exact rowEval4962 x
  · exact rowEval4963 x
  · exact rowEval4964 x
  · exact rowEval4965 x
  · exact rowEval4966 x
  · exact rowEval4967 x

theorem entryEval20_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_10 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck20_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_10]

def rows20_11 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4968, row4969, row4970, row4971, row4972, row4973, row4974, row4975, row4976, row4977, row4978, row4979, row4980, row4981, row4982, row4983, row4984, row4985]

theorem entryCheck20_11 : entry20_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_11 k)) := by decide +kernel

theorem rowsSound20_11 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval4968 x
  · exact rowEval4969 x
  · exact rowEval4970 x
  · exact rowEval4971 x
  · exact rowEval4972 x
  · exact rowEval4973 x
  · exact rowEval4974 x
  · exact rowEval4975 x
  · exact rowEval4976 x
  · exact rowEval4977 x
  · exact rowEval4978 x
  · exact rowEval4979 x
  · exact rowEval4980 x
  · exact rowEval4981 x
  · exact rowEval4982 x
  · exact rowEval4983 x
  · exact rowEval4984 x
  · exact rowEval4985 x

theorem entryEval20_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_11 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck20_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_11]

def rows20_12 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4986, row4987, row4988, row4989, row4990, row4991, row4992, row4993, row4994, row4995, row4996, row4997, row4998, row4999, row5000, row5001, row5002, row5003]

theorem entryCheck20_12 : entry20_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_12 k)) := by decide +kernel

theorem rowsSound20_12 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval4986 x
  · exact rowEval4987 x
  · exact rowEval4988 x
  · exact rowEval4989 x
  · exact rowEval4990 x
  · exact rowEval4991 x
  · exact rowEval4992 x
  · exact rowEval4993 x
  · exact rowEval4994 x
  · exact rowEval4995 x
  · exact rowEval4996 x
  · exact rowEval4997 x
  · exact rowEval4998 x
  · exact rowEval4999 x
  · exact rowEval5000 x
  · exact rowEval5001 x
  · exact rowEval5002 x
  · exact rowEval5003 x

theorem entryEval20_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_12 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck20_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_12]

def rows20_13 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5004, row5005, row5006, row5007, row5008, row5009, row5010, row5011, row5012, row5013, row5014, row5015, row5016, row5017, row5018, row5019, row5020, row5021]

theorem entryCheck20_13 : entry20_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_13 k)) := by decide +kernel

theorem rowsSound20_13 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval5004 x
  · exact rowEval5005 x
  · exact rowEval5006 x
  · exact rowEval5007 x
  · exact rowEval5008 x
  · exact rowEval5009 x
  · exact rowEval5010 x
  · exact rowEval5011 x
  · exact rowEval5012 x
  · exact rowEval5013 x
  · exact rowEval5014 x
  · exact rowEval5015 x
  · exact rowEval5016 x
  · exact rowEval5017 x
  · exact rowEval5018 x
  · exact rowEval5019 x
  · exact rowEval5020 x
  · exact rowEval5021 x

theorem entryEval20_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_13 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck20_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_13]

def rows20_14 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5022, row5023, row5024, row5025, row5026, row5027, row5028, row5029, row5030, row5031, row5032, row5033, row5034, row5035, row5036, row5037, row5038, row5039]

theorem entryCheck20_14 : entry20_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_14 k)) := by decide +kernel

theorem rowsSound20_14 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval5022 x
  · exact rowEval5023 x
  · exact rowEval5024 x
  · exact rowEval5025 x
  · exact rowEval5026 x
  · exact rowEval5027 x
  · exact rowEval5028 x
  · exact rowEval5029 x
  · exact rowEval5030 x
  · exact rowEval5031 x
  · exact rowEval5032 x
  · exact rowEval5033 x
  · exact rowEval5034 x
  · exact rowEval5035 x
  · exact rowEval5036 x
  · exact rowEval5037 x
  · exact rowEval5038 x
  · exact rowEval5039 x

theorem entryEval20_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_14 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck20_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_14]

def rows20_15 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5040, row5041, row5042, row5043, row5044, row5045, row5046, row5047, row5048, row5049, row5050, row5051, row5052, row5053, row5054, row5055, row5056, row5057]

theorem entryCheck20_15 : entry20_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_15 k)) := by decide +kernel

theorem rowsSound20_15 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form15) x := by
  fin_cases k
  · exact rowEval5040 x
  · exact rowEval5041 x
  · exact rowEval5042 x
  · exact rowEval5043 x
  · exact rowEval5044 x
  · exact rowEval5045 x
  · exact rowEval5046 x
  · exact rowEval5047 x
  · exact rowEval5048 x
  · exact rowEval5049 x
  · exact rowEval5050 x
  · exact rowEval5051 x
  · exact rowEval5052 x
  · exact rowEval5053 x
  · exact rowEval5054 x
  · exact rowEval5055 x
  · exact rowEval5056 x
  · exact rowEval5057 x

theorem entryEval20_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_15 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form15 B := by
  rw [entryCheck20_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_15]

def rows20_16 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5058, row5059, row5060, row5061, row5062, row5063, row5064, row5065, row5066, row5067, row5068, row5069, row5070, row5071, row5072, row5073, row5074, row5075]

theorem entryCheck20_16 : entry20_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_16 k)) := by decide +kernel

theorem rowsSound20_16 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval5058 x
  · exact rowEval5059 x
  · exact rowEval5060 x
  · exact rowEval5061 x
  · exact rowEval5062 x
  · exact rowEval5063 x
  · exact rowEval5064 x
  · exact rowEval5065 x
  · exact rowEval5066 x
  · exact rowEval5067 x
  · exact rowEval5068 x
  · exact rowEval5069 x
  · exact rowEval5070 x
  · exact rowEval5071 x
  · exact rowEval5072 x
  · exact rowEval5073 x
  · exact rowEval5074 x
  · exact rowEval5075 x

theorem entryEval20_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_16 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck20_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_16]

def rows20_17 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5076, row5077, row5078, row5079, row5080, row5081, row5082, row5083, row5084, row5085, row5086, row5087, row5088, row5089, row5090, row5091, row5092, row5093]

theorem entryCheck20_17 : entry20_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_17 k)) := by decide +kernel

theorem rowsSound20_17 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form17) x := by
  fin_cases k
  · exact rowEval5076 x
  · exact rowEval5077 x
  · exact rowEval5078 x
  · exact rowEval5079 x
  · exact rowEval5080 x
  · exact rowEval5081 x
  · exact rowEval5082 x
  · exact rowEval5083 x
  · exact rowEval5084 x
  · exact rowEval5085 x
  · exact rowEval5086 x
  · exact rowEval5087 x
  · exact rowEval5088 x
  · exact rowEval5089 x
  · exact rowEval5090 x
  · exact rowEval5091 x
  · exact rowEval5092 x
  · exact rowEval5093 x

theorem entryEval20_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_17 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form17 B := by
  rw [entryCheck20_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_17]

def rows20_18 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5094, row5095, row5096, row5097, row5098, row5099, row5100, row5101, row5102, row5103, row5104, row5105, row5106, row5107, row5108, row5109, row5110, row5111]

theorem entryCheck20_18 : entry20_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_18 k)) := by decide +kernel

theorem rowsSound20_18 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form18) x := by
  fin_cases k
  · exact rowEval5094 x
  · exact rowEval5095 x
  · exact rowEval5096 x
  · exact rowEval5097 x
  · exact rowEval5098 x
  · exact rowEval5099 x
  · exact rowEval5100 x
  · exact rowEval5101 x
  · exact rowEval5102 x
  · exact rowEval5103 x
  · exact rowEval5104 x
  · exact rowEval5105 x
  · exact rowEval5106 x
  · exact rowEval5107 x
  · exact rowEval5108 x
  · exact rowEval5109 x
  · exact rowEval5110 x
  · exact rowEval5111 x

theorem entryEval20_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_18 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form18 B := by
  rw [entryCheck20_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_18]

def rows20_19 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5112, row5113, row5114, row5115, row5116, row5117, row5118, row5119, row5120, row5121, row5122, row5123, row5124, row5125, row5126, row5127, row5128, row5129]

theorem entryCheck20_19 : entry20_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_19 k)) := by decide +kernel

theorem rowsSound20_19 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form19) x := by
  fin_cases k
  · exact rowEval5112 x
  · exact rowEval5113 x
  · exact rowEval5114 x
  · exact rowEval5115 x
  · exact rowEval5116 x
  · exact rowEval5117 x
  · exact rowEval5118 x
  · exact rowEval5119 x
  · exact rowEval5120 x
  · exact rowEval5121 x
  · exact rowEval5122 x
  · exact rowEval5123 x
  · exact rowEval5124 x
  · exact rowEval5125 x
  · exact rowEval5126 x
  · exact rowEval5127 x
  · exact rowEval5128 x
  · exact rowEval5129 x

theorem entryEval20_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_19 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form19 B := by
  rw [entryCheck20_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_19]

def rows20_20 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5130, row5131, row5132, row5133, row5134, row5135, row5136, row5137, row5138, row5139, row5140, row5141, row5142, row5143, row5144, row5145, row5146, row5147]

theorem entryCheck20_20 : entry20_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_20 k)) := by decide +kernel

theorem rowsSound20_20 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form20) x := by
  fin_cases k
  · exact rowEval5130 x
  · exact rowEval5131 x
  · exact rowEval5132 x
  · exact rowEval5133 x
  · exact rowEval5134 x
  · exact rowEval5135 x
  · exact rowEval5136 x
  · exact rowEval5137 x
  · exact rowEval5138 x
  · exact rowEval5139 x
  · exact rowEval5140 x
  · exact rowEval5141 x
  · exact rowEval5142 x
  · exact rowEval5143 x
  · exact rowEval5144 x
  · exact rowEval5145 x
  · exact rowEval5146 x
  · exact rowEval5147 x

theorem entryEval20_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_20 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form20 B := by
  rw [entryCheck20_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_20]

end MUB6.Certificate.GramEntries.Block1

end OAI
