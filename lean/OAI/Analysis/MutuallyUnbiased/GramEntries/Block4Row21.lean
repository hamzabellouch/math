import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block164
import OAI.Analysis.MutuallyUnbiased.GramRows.Block165
import OAI.Analysis.MutuallyUnbiased.GramRows.Block166
import OAI.Analysis.MutuallyUnbiased.GramRows.Block167

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows21_0 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row17989, row17990, row17991, row17992, row17993, row17994, row17995, row17996, row17997, row17998, row17999, row18000, row18001, row18002, row18003, row18004, row18005, row18006, row18007, row18008]

theorem entryCheck21_0 : entry21_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_0 k)) := by decide +kernel

theorem rowsSound21_0 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17989 x
  · exact rowEval17990 x
  · exact rowEval17991 x
  · exact rowEval17992 x
  · exact rowEval17993 x
  · exact rowEval17994 x
  · exact rowEval17995 x
  · exact rowEval17996 x
  · exact rowEval17997 x
  · exact rowEval17998 x
  · exact rowEval17999 x
  · exact rowEval18000 x
  · exact rowEval18001 x
  · exact rowEval18002 x
  · exact rowEval18003 x
  · exact rowEval18004 x
  · exact rowEval18005 x
  · exact rowEval18006 x
  · exact rowEval18007 x
  · exact rowEval18008 x

theorem entryEval21_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_0 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck21_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_0]

def rows21_1 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18009, row18010, row18011, row18012, row18013, row18014, row18015, row18016, row18017, row18018, row18019, row18020, row18021, row18022, row18023, row18024, row18025, row18026, row18027, row18028]

theorem entryCheck21_1 : entry21_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_1 k)) := by decide +kernel

theorem rowsSound21_1 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval18009 x
  · exact rowEval18010 x
  · exact rowEval18011 x
  · exact rowEval18012 x
  · exact rowEval18013 x
  · exact rowEval18014 x
  · exact rowEval18015 x
  · exact rowEval18016 x
  · exact rowEval18017 x
  · exact rowEval18018 x
  · exact rowEval18019 x
  · exact rowEval18020 x
  · exact rowEval18021 x
  · exact rowEval18022 x
  · exact rowEval18023 x
  · exact rowEval18024 x
  · exact rowEval18025 x
  · exact rowEval18026 x
  · exact rowEval18027 x
  · exact rowEval18028 x

theorem entryEval21_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_1 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck21_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_1]

def rows21_2 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18029, row18030, row18031, row18032, row18033, row18034, row18035, row18036, row18037, row18038, row18039, row18040, row18041, row18042, row18043, row18044, row18045, row18046, row18047, row18048]

theorem entryCheck21_2 : entry21_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_2 k)) := by decide +kernel

theorem rowsSound21_2 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval18029 x
  · exact rowEval18030 x
  · exact rowEval18031 x
  · exact rowEval18032 x
  · exact rowEval18033 x
  · exact rowEval18034 x
  · exact rowEval18035 x
  · exact rowEval18036 x
  · exact rowEval18037 x
  · exact rowEval18038 x
  · exact rowEval18039 x
  · exact rowEval18040 x
  · exact rowEval18041 x
  · exact rowEval18042 x
  · exact rowEval18043 x
  · exact rowEval18044 x
  · exact rowEval18045 x
  · exact rowEval18046 x
  · exact rowEval18047 x
  · exact rowEval18048 x

theorem entryEval21_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_2 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck21_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_2]

def rows21_3 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18049, row18050, row18051, row18052, row18053, row18054, row18055, row18056, row18057, row18058, row18059, row18060, row18061, row18062, row18063, row18064, row18065, row18066, row18067, row18068]

theorem entryCheck21_3 : entry21_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_3 k)) := by decide +kernel

theorem rowsSound21_3 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval18049 x
  · exact rowEval18050 x
  · exact rowEval18051 x
  · exact rowEval18052 x
  · exact rowEval18053 x
  · exact rowEval18054 x
  · exact rowEval18055 x
  · exact rowEval18056 x
  · exact rowEval18057 x
  · exact rowEval18058 x
  · exact rowEval18059 x
  · exact rowEval18060 x
  · exact rowEval18061 x
  · exact rowEval18062 x
  · exact rowEval18063 x
  · exact rowEval18064 x
  · exact rowEval18065 x
  · exact rowEval18066 x
  · exact rowEval18067 x
  · exact rowEval18068 x

theorem entryEval21_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_3 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck21_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_3]

def rows21_4 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18069, row18070, row18071, row18072, row18073, row18074, row18075, row18076, row18077, row18078, row18079, row18080, row18081, row18082, row18083, row18084, row18085, row18086, row18087, row18088]

theorem entryCheck21_4 : entry21_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_4 k)) := by decide +kernel

theorem rowsSound21_4 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval18069 x
  · exact rowEval18070 x
  · exact rowEval18071 x
  · exact rowEval18072 x
  · exact rowEval18073 x
  · exact rowEval18074 x
  · exact rowEval18075 x
  · exact rowEval18076 x
  · exact rowEval18077 x
  · exact rowEval18078 x
  · exact rowEval18079 x
  · exact rowEval18080 x
  · exact rowEval18081 x
  · exact rowEval18082 x
  · exact rowEval18083 x
  · exact rowEval18084 x
  · exact rowEval18085 x
  · exact rowEval18086 x
  · exact rowEval18087 x
  · exact rowEval18088 x

theorem entryEval21_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_4 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck21_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_4]

def rows21_5 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18089, row18090, row18091, row18092, row18093, row18094, row18095, row18096, row18097, row18098, row18099, row18100, row18101, row18102, row18103, row18104, row18105, row18106, row18107, row18108]

theorem entryCheck21_5 : entry21_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_5 k)) := by decide +kernel

theorem rowsSound21_5 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval18089 x
  · exact rowEval18090 x
  · exact rowEval18091 x
  · exact rowEval18092 x
  · exact rowEval18093 x
  · exact rowEval18094 x
  · exact rowEval18095 x
  · exact rowEval18096 x
  · exact rowEval18097 x
  · exact rowEval18098 x
  · exact rowEval18099 x
  · exact rowEval18100 x
  · exact rowEval18101 x
  · exact rowEval18102 x
  · exact rowEval18103 x
  · exact rowEval18104 x
  · exact rowEval18105 x
  · exact rowEval18106 x
  · exact rowEval18107 x
  · exact rowEval18108 x

theorem entryEval21_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_5 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck21_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_5]

def rows21_6 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18109, row18110, row18111, row18112, row18113, row18114, row18115, row18116, row18117, row18118, row18119, row18120, row18121, row18122, row18123, row18124, row18125, row18126, row18127, row18128]

theorem entryCheck21_6 : entry21_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_6 k)) := by decide +kernel

theorem rowsSound21_6 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval18109 x
  · exact rowEval18110 x
  · exact rowEval18111 x
  · exact rowEval18112 x
  · exact rowEval18113 x
  · exact rowEval18114 x
  · exact rowEval18115 x
  · exact rowEval18116 x
  · exact rowEval18117 x
  · exact rowEval18118 x
  · exact rowEval18119 x
  · exact rowEval18120 x
  · exact rowEval18121 x
  · exact rowEval18122 x
  · exact rowEval18123 x
  · exact rowEval18124 x
  · exact rowEval18125 x
  · exact rowEval18126 x
  · exact rowEval18127 x
  · exact rowEval18128 x

theorem entryEval21_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_6 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck21_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_6]

def rows21_7 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18129, row18130, row18131, row18132, row18133, row18134, row18135, row18136, row18137, row18138, row18139, row18140, row18141, row18142, row18143, row18144, row18145, row18146, row18147, row18148]

theorem entryCheck21_7 : entry21_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_7 k)) := by decide +kernel

theorem rowsSound21_7 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval18129 x
  · exact rowEval18130 x
  · exact rowEval18131 x
  · exact rowEval18132 x
  · exact rowEval18133 x
  · exact rowEval18134 x
  · exact rowEval18135 x
  · exact rowEval18136 x
  · exact rowEval18137 x
  · exact rowEval18138 x
  · exact rowEval18139 x
  · exact rowEval18140 x
  · exact rowEval18141 x
  · exact rowEval18142 x
  · exact rowEval18143 x
  · exact rowEval18144 x
  · exact rowEval18145 x
  · exact rowEval18146 x
  · exact rowEval18147 x
  · exact rowEval18148 x

theorem entryEval21_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_7 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck21_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_7]

def rows21_8 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18149, row18150, row18151, row18152, row18153, row18154, row18155, row18156, row18157, row18158, row18159, row18160, row18161, row18162, row18163, row18164, row18165, row18166, row18167, row18168]

theorem entryCheck21_8 : entry21_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_8 k)) := by decide +kernel

theorem rowsSound21_8 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval18149 x
  · exact rowEval18150 x
  · exact rowEval18151 x
  · exact rowEval18152 x
  · exact rowEval18153 x
  · exact rowEval18154 x
  · exact rowEval18155 x
  · exact rowEval18156 x
  · exact rowEval18157 x
  · exact rowEval18158 x
  · exact rowEval18159 x
  · exact rowEval18160 x
  · exact rowEval18161 x
  · exact rowEval18162 x
  · exact rowEval18163 x
  · exact rowEval18164 x
  · exact rowEval18165 x
  · exact rowEval18166 x
  · exact rowEval18167 x
  · exact rowEval18168 x

theorem entryEval21_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_8 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck21_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_8]

def rows21_9 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18169, row18170, row18171, row18172, row18173, row18174, row18175, row18176, row18177, row18178, row18179, row18180, row18181, row18182, row18183, row18184, row18185, row18186, row18187, row18188]

theorem entryCheck21_9 : entry21_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_9 k)) := by decide +kernel

theorem rowsSound21_9 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval18169 x
  · exact rowEval18170 x
  · exact rowEval18171 x
  · exact rowEval18172 x
  · exact rowEval18173 x
  · exact rowEval18174 x
  · exact rowEval18175 x
  · exact rowEval18176 x
  · exact rowEval18177 x
  · exact rowEval18178 x
  · exact rowEval18179 x
  · exact rowEval18180 x
  · exact rowEval18181 x
  · exact rowEval18182 x
  · exact rowEval18183 x
  · exact rowEval18184 x
  · exact rowEval18185 x
  · exact rowEval18186 x
  · exact rowEval18187 x
  · exact rowEval18188 x

theorem entryEval21_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_9 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck21_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_9]

def rows21_10 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18189, row18190, row18191, row18192, row18193, row18194, row18195, row18196, row18197, row18198, row18199, row18200, row18201, row18202, row18203, row18204, row18205, row18206, row18207, row18208]

theorem entryCheck21_10 : entry21_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_10 k)) := by decide +kernel

theorem rowsSound21_10 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval18189 x
  · exact rowEval18190 x
  · exact rowEval18191 x
  · exact rowEval18192 x
  · exact rowEval18193 x
  · exact rowEval18194 x
  · exact rowEval18195 x
  · exact rowEval18196 x
  · exact rowEval18197 x
  · exact rowEval18198 x
  · exact rowEval18199 x
  · exact rowEval18200 x
  · exact rowEval18201 x
  · exact rowEval18202 x
  · exact rowEval18203 x
  · exact rowEval18204 x
  · exact rowEval18205 x
  · exact rowEval18206 x
  · exact rowEval18207 x
  · exact rowEval18208 x

theorem entryEval21_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_10 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck21_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_10]

def rows21_11 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18209, row18210, row18211, row18212, row18213, row18214, row18215, row18216, row18217, row18218, row18219, row18220, row18221, row18222, row18223, row18224, row18225, row18226, row18227, row18228]

theorem entryCheck21_11 : entry21_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_11 k)) := by decide +kernel

theorem rowsSound21_11 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval18209 x
  · exact rowEval18210 x
  · exact rowEval18211 x
  · exact rowEval18212 x
  · exact rowEval18213 x
  · exact rowEval18214 x
  · exact rowEval18215 x
  · exact rowEval18216 x
  · exact rowEval18217 x
  · exact rowEval18218 x
  · exact rowEval18219 x
  · exact rowEval18220 x
  · exact rowEval18221 x
  · exact rowEval18222 x
  · exact rowEval18223 x
  · exact rowEval18224 x
  · exact rowEval18225 x
  · exact rowEval18226 x
  · exact rowEval18227 x
  · exact rowEval18228 x

theorem entryEval21_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_11 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck21_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_11]

def rows21_12 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18229, row18230, row18231, row18232, row18233, row18234, row18235, row18236, row18237, row18238, row18239, row18240, row18241, row18242, row18243, row18244, row18245, row18246, row18247, row18248]

theorem entryCheck21_12 : entry21_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_12 k)) := by decide +kernel

theorem rowsSound21_12 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval18229 x
  · exact rowEval18230 x
  · exact rowEval18231 x
  · exact rowEval18232 x
  · exact rowEval18233 x
  · exact rowEval18234 x
  · exact rowEval18235 x
  · exact rowEval18236 x
  · exact rowEval18237 x
  · exact rowEval18238 x
  · exact rowEval18239 x
  · exact rowEval18240 x
  · exact rowEval18241 x
  · exact rowEval18242 x
  · exact rowEval18243 x
  · exact rowEval18244 x
  · exact rowEval18245 x
  · exact rowEval18246 x
  · exact rowEval18247 x
  · exact rowEval18248 x

theorem entryEval21_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_12 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck21_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_12]

def rows21_13 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18249, row18250, row18251, row18252, row18253, row18254, row18255, row18256, row18257, row18258, row18259, row18260, row18261, row18262, row18263, row18264, row18265, row18266, row18267, row18268]

theorem entryCheck21_13 : entry21_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_13 k)) := by decide +kernel

theorem rowsSound21_13 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval18249 x
  · exact rowEval18250 x
  · exact rowEval18251 x
  · exact rowEval18252 x
  · exact rowEval18253 x
  · exact rowEval18254 x
  · exact rowEval18255 x
  · exact rowEval18256 x
  · exact rowEval18257 x
  · exact rowEval18258 x
  · exact rowEval18259 x
  · exact rowEval18260 x
  · exact rowEval18261 x
  · exact rowEval18262 x
  · exact rowEval18263 x
  · exact rowEval18264 x
  · exact rowEval18265 x
  · exact rowEval18266 x
  · exact rowEval18267 x
  · exact rowEval18268 x

theorem entryEval21_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_13 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck21_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_13]

def rows21_14 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18269, row18270, row18271, row18272, row18273, row18274, row18275, row18276, row18277, row18278, row18279, row18280, row18281, row18282, row18283, row18284, row18285, row18286, row18287, row18288]

theorem entryCheck21_14 : entry21_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_14 k)) := by decide +kernel

theorem rowsSound21_14 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form14) x := by
  fin_cases k
  · exact rowEval18269 x
  · exact rowEval18270 x
  · exact rowEval18271 x
  · exact rowEval18272 x
  · exact rowEval18273 x
  · exact rowEval18274 x
  · exact rowEval18275 x
  · exact rowEval18276 x
  · exact rowEval18277 x
  · exact rowEval18278 x
  · exact rowEval18279 x
  · exact rowEval18280 x
  · exact rowEval18281 x
  · exact rowEval18282 x
  · exact rowEval18283 x
  · exact rowEval18284 x
  · exact rowEval18285 x
  · exact rowEval18286 x
  · exact rowEval18287 x
  · exact rowEval18288 x

theorem entryEval21_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_14 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form14 B := by
  rw [entryCheck21_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_14]

def rows21_15 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18289, row18290, row18291, row18292, row18293, row18294, row18295, row18296, row18297, row18298, row18299, row18300, row18301, row18302, row18303, row18304, row18305, row18306, row18307, row18308]

theorem entryCheck21_15 : entry21_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_15 k)) := by decide +kernel

theorem rowsSound21_15 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form15) x := by
  fin_cases k
  · exact rowEval18289 x
  · exact rowEval18290 x
  · exact rowEval18291 x
  · exact rowEval18292 x
  · exact rowEval18293 x
  · exact rowEval18294 x
  · exact rowEval18295 x
  · exact rowEval18296 x
  · exact rowEval18297 x
  · exact rowEval18298 x
  · exact rowEval18299 x
  · exact rowEval18300 x
  · exact rowEval18301 x
  · exact rowEval18302 x
  · exact rowEval18303 x
  · exact rowEval18304 x
  · exact rowEval18305 x
  · exact rowEval18306 x
  · exact rowEval18307 x
  · exact rowEval18308 x

theorem entryEval21_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_15 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form15 B := by
  rw [entryCheck21_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_15]

def rows21_16 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18309, row18310, row18311, row18312, row18313, row18314, row18315, row18316, row18317, row18318, row18319, row18320, row18321, row18322, row18323, row18324, row18325, row18326, row18327, row18328]

theorem entryCheck21_16 : entry21_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_16 k)) := by decide +kernel

theorem rowsSound21_16 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form16) x := by
  fin_cases k
  · exact rowEval18309 x
  · exact rowEval18310 x
  · exact rowEval18311 x
  · exact rowEval18312 x
  · exact rowEval18313 x
  · exact rowEval18314 x
  · exact rowEval18315 x
  · exact rowEval18316 x
  · exact rowEval18317 x
  · exact rowEval18318 x
  · exact rowEval18319 x
  · exact rowEval18320 x
  · exact rowEval18321 x
  · exact rowEval18322 x
  · exact rowEval18323 x
  · exact rowEval18324 x
  · exact rowEval18325 x
  · exact rowEval18326 x
  · exact rowEval18327 x
  · exact rowEval18328 x

theorem entryEval21_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_16 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form16 B := by
  rw [entryCheck21_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_16]

def rows21_17 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18329, row18330, row18331, row18332, row18333, row18334, row18335, row18336, row18337, row18338, row18339, row18340, row18341, row18342, row18343, row18344, row18345, row18346, row18347, row18348]

theorem entryCheck21_17 : entry21_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_17 k)) := by decide +kernel

theorem rowsSound21_17 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval18329 x
  · exact rowEval18330 x
  · exact rowEval18331 x
  · exact rowEval18332 x
  · exact rowEval18333 x
  · exact rowEval18334 x
  · exact rowEval18335 x
  · exact rowEval18336 x
  · exact rowEval18337 x
  · exact rowEval18338 x
  · exact rowEval18339 x
  · exact rowEval18340 x
  · exact rowEval18341 x
  · exact rowEval18342 x
  · exact rowEval18343 x
  · exact rowEval18344 x
  · exact rowEval18345 x
  · exact rowEval18346 x
  · exact rowEval18347 x
  · exact rowEval18348 x

theorem entryEval21_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_17 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck21_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_17]

def rows21_18 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18349, row18350, row18351, row18352, row18353, row18354, row18355, row18356, row18357, row18358, row18359, row18360, row18361, row18362, row18363, row18364, row18365, row18366, row18367, row18368]

theorem entryCheck21_18 : entry21_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_18 k)) := by decide +kernel

theorem rowsSound21_18 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form18) x := by
  fin_cases k
  · exact rowEval18349 x
  · exact rowEval18350 x
  · exact rowEval18351 x
  · exact rowEval18352 x
  · exact rowEval18353 x
  · exact rowEval18354 x
  · exact rowEval18355 x
  · exact rowEval18356 x
  · exact rowEval18357 x
  · exact rowEval18358 x
  · exact rowEval18359 x
  · exact rowEval18360 x
  · exact rowEval18361 x
  · exact rowEval18362 x
  · exact rowEval18363 x
  · exact rowEval18364 x
  · exact rowEval18365 x
  · exact rowEval18366 x
  · exact rowEval18367 x
  · exact rowEval18368 x

theorem entryEval21_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_18 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form18 B := by
  rw [entryCheck21_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_18]

def rows21_19 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18369, row18370, row18371, row18372, row18373, row18374, row18375, row18376, row18377, row18378, row18379, row18380, row18381, row18382, row18383, row18384, row18385, row18386, row18387, row18388]

theorem entryCheck21_19 : entry21_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_19 k)) := by decide +kernel

theorem rowsSound21_19 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form19) x := by
  fin_cases k
  · exact rowEval18369 x
  · exact rowEval18370 x
  · exact rowEval18371 x
  · exact rowEval18372 x
  · exact rowEval18373 x
  · exact rowEval18374 x
  · exact rowEval18375 x
  · exact rowEval18376 x
  · exact rowEval18377 x
  · exact rowEval18378 x
  · exact rowEval18379 x
  · exact rowEval18380 x
  · exact rowEval18381 x
  · exact rowEval18382 x
  · exact rowEval18383 x
  · exact rowEval18384 x
  · exact rowEval18385 x
  · exact rowEval18386 x
  · exact rowEval18387 x
  · exact rowEval18388 x

theorem entryEval21_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_19 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form19 B := by
  rw [entryCheck21_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_19]

def rows21_20 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18389, row18390, row18391, row18392, row18393, row18394, row18395, row18396, row18397, row18398, row18399, row18400, row18401, row18402, row18403, row18404, row18405, row18406, row18407, row18408]

theorem entryCheck21_20 : entry21_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_20 k)) := by decide +kernel

theorem rowsSound21_20 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form20) x := by
  fin_cases k
  · exact rowEval18389 x
  · exact rowEval18390 x
  · exact rowEval18391 x
  · exact rowEval18392 x
  · exact rowEval18393 x
  · exact rowEval18394 x
  · exact rowEval18395 x
  · exact rowEval18396 x
  · exact rowEval18397 x
  · exact rowEval18398 x
  · exact rowEval18399 x
  · exact rowEval18400 x
  · exact rowEval18401 x
  · exact rowEval18402 x
  · exact rowEval18403 x
  · exact rowEval18404 x
  · exact rowEval18405 x
  · exact rowEval18406 x
  · exact rowEval18407 x
  · exact rowEval18408 x

theorem entryEval21_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_20 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form20 B := by
  rw [entryCheck21_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_20]

def rows21_21 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18409, row18410, row18411, row18412, row18413, row18414, row18415, row18416, row18417, row18418, row18419, row18420, row18421, row18422, row18423, row18424, row18425, row18426, row18427, row18428]

theorem entryCheck21_21 : entry21_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_21 k)) := by decide +kernel

theorem rowsSound21_21 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form21) x := by
  fin_cases k
  · exact rowEval18409 x
  · exact rowEval18410 x
  · exact rowEval18411 x
  · exact rowEval18412 x
  · exact rowEval18413 x
  · exact rowEval18414 x
  · exact rowEval18415 x
  · exact rowEval18416 x
  · exact rowEval18417 x
  · exact rowEval18418 x
  · exact rowEval18419 x
  · exact rowEval18420 x
  · exact rowEval18421 x
  · exact rowEval18422 x
  · exact rowEval18423 x
  · exact rowEval18424 x
  · exact rowEval18425 x
  · exact rowEval18426 x
  · exact rowEval18427 x
  · exact rowEval18428 x

theorem entryEval21_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_21 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form21 B := by
  rw [entryCheck21_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_21]

end MUB6.Certificate.GramEntries.Block4

end OAI
