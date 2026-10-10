import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block134

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14105, row14106, row14107, row14108, row14109, row14110, row14111, row14112, row14113, row14114]

theorem entryCheck9_0 : entry9_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_0 k)) := by decide +kernel

theorem rowsSound9_0 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14105 x
  · exact rowEval14106 x
  · exact rowEval14107 x
  · exact rowEval14108 x
  · exact rowEval14109 x
  · exact rowEval14110 x
  · exact rowEval14111 x
  · exact rowEval14112 x
  · exact rowEval14113 x
  · exact rowEval14114 x

theorem entryEval9_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_0 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck9_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_0]

def rows9_1 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14115, row14116, row14117, row14118, row14119, row14120, row14121, row14122, row14123, row14124]

theorem entryCheck9_1 : entry9_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_1 k)) := by decide +kernel

theorem rowsSound9_1 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval14115 x
  · exact rowEval14116 x
  · exact rowEval14117 x
  · exact rowEval14118 x
  · exact rowEval14119 x
  · exact rowEval14120 x
  · exact rowEval14121 x
  · exact rowEval14122 x
  · exact rowEval14123 x
  · exact rowEval14124 x

theorem entryEval9_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_1 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck9_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_1]

def rows9_2 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14125, row14126, row14127, row14128, row14129, row14130, row14131, row14132, row14133, row14134]

theorem entryCheck9_2 : entry9_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_2 k)) := by decide +kernel

theorem rowsSound9_2 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval14125 x
  · exact rowEval14126 x
  · exact rowEval14127 x
  · exact rowEval14128 x
  · exact rowEval14129 x
  · exact rowEval14130 x
  · exact rowEval14131 x
  · exact rowEval14132 x
  · exact rowEval14133 x
  · exact rowEval14134 x

theorem entryEval9_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_2 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck9_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_2]

def rows9_3 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14135, row14136, row14137, row14138, row14139, row14140, row14141, row14142, row14143, row14144]

theorem entryCheck9_3 : entry9_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_3 k)) := by decide +kernel

theorem rowsSound9_3 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval14135 x
  · exact rowEval14136 x
  · exact rowEval14137 x
  · exact rowEval14138 x
  · exact rowEval14139 x
  · exact rowEval14140 x
  · exact rowEval14141 x
  · exact rowEval14142 x
  · exact rowEval14143 x
  · exact rowEval14144 x

theorem entryEval9_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_3 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck9_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_3]

def rows9_4 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14145, row14146, row14147, row14148, row14149, row14150, row14151, row14152, row14153, row14154]

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14145 x
  · exact rowEval14146 x
  · exact rowEval14147 x
  · exact rowEval14148 x
  · exact rowEval14149 x
  · exact rowEval14150 x
  · exact rowEval14151 x
  · exact rowEval14152 x
  · exact rowEval14153 x
  · exact rowEval14154 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

def rows9_5 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14155, row14156, row14157, row14158, row14159, row14160, row14161, row14162, row14163, row14164]

theorem entryCheck9_5 : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

theorem rowsSound9_5 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14155 x
  · exact rowEval14156 x
  · exact rowEval14157 x
  · exact rowEval14158 x
  · exact rowEval14159 x
  · exact rowEval14160 x
  · exact rowEval14161 x
  · exact rowEval14162 x
  · exact rowEval14163 x
  · exact rowEval14164 x

theorem entryEval9_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_5 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck9_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_5]

def rows9_6 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14165, row14166, row14167, row14168, row14169, row14170, row14171, row14172, row14173, row14174]

theorem entryCheck9_6 : entry9_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_6 k)) := by decide +kernel

theorem rowsSound9_6 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval14165 x
  · exact rowEval14166 x
  · exact rowEval14167 x
  · exact rowEval14168 x
  · exact rowEval14169 x
  · exact rowEval14170 x
  · exact rowEval14171 x
  · exact rowEval14172 x
  · exact rowEval14173 x
  · exact rowEval14174 x

theorem entryEval9_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_6 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck9_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_6]

def rows9_7 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14175, row14176, row14177, row14178, row14179, row14180, row14181, row14182, row14183, row14184]

theorem entryCheck9_7 : entry9_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_7 k)) := by decide +kernel

theorem rowsSound9_7 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval14175 x
  · exact rowEval14176 x
  · exact rowEval14177 x
  · exact rowEval14178 x
  · exact rowEval14179 x
  · exact rowEval14180 x
  · exact rowEval14181 x
  · exact rowEval14182 x
  · exact rowEval14183 x
  · exact rowEval14184 x

theorem entryEval9_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_7 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck9_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_7]

def rows9_8 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14185, row14186, row14187, row14188, row14189, row14190, row14191, row14192, row14193, row14194]

theorem entryCheck9_8 : entry9_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_8 k)) := by decide +kernel

theorem rowsSound9_8 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval14185 x
  · exact rowEval14186 x
  · exact rowEval14187 x
  · exact rowEval14188 x
  · exact rowEval14189 x
  · exact rowEval14190 x
  · exact rowEval14191 x
  · exact rowEval14192 x
  · exact rowEval14193 x
  · exact rowEval14194 x

theorem entryEval9_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_8 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck9_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_8]

def rows9_9 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14195, row14196, row14197, row14198, row14199, row14200, row14201, row14202, row14203, row14204]

theorem entryCheck9_9 : entry9_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_9 k)) := by decide +kernel

theorem rowsSound9_9 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval14195 x
  · exact rowEval14196 x
  · exact rowEval14197 x
  · exact rowEval14198 x
  · exact rowEval14199 x
  · exact rowEval14200 x
  · exact rowEval14201 x
  · exact rowEval14202 x
  · exact rowEval14203 x
  · exact rowEval14204 x

theorem entryEval9_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_9 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck9_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_9]

end MUB6.Certificate.GramEntries.Block4

end OAI
