import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block173
import OAI.Analysis.MutuallyUnbiased.GramRows.Block174

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19079, row19080, row19081, row19082, row19083, row19084, row19085, row19086, row19087, row19088, row19089, row19090, row19091, row19092, row19093, row19094, row19095, row19096, row19097, row19098]

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19079 x
  · exact rowEval19080 x
  · exact rowEval19081 x
  · exact rowEval19082 x
  · exact rowEval19083 x
  · exact rowEval19084 x
  · exact rowEval19085 x
  · exact rowEval19086 x
  · exact rowEval19087 x
  · exact rowEval19088 x
  · exact rowEval19089 x
  · exact rowEval19090 x
  · exact rowEval19091 x
  · exact rowEval19092 x
  · exact rowEval19093 x
  · exact rowEval19094 x
  · exact rowEval19095 x
  · exact rowEval19096 x
  · exact rowEval19097 x
  · exact rowEval19098 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

def rows7_1 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19099, row19100, row19101, row19102, row19103, row19104, row19105, row19106, row19107, row19108, row19109, row19110, row19111, row19112, row19113, row19114, row19115, row19116, row19117, row19118]

theorem entryCheck7_1 : entry7_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_1 k)) := by decide +kernel

theorem rowsSound7_1 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19099 x
  · exact rowEval19100 x
  · exact rowEval19101 x
  · exact rowEval19102 x
  · exact rowEval19103 x
  · exact rowEval19104 x
  · exact rowEval19105 x
  · exact rowEval19106 x
  · exact rowEval19107 x
  · exact rowEval19108 x
  · exact rowEval19109 x
  · exact rowEval19110 x
  · exact rowEval19111 x
  · exact rowEval19112 x
  · exact rowEval19113 x
  · exact rowEval19114 x
  · exact rowEval19115 x
  · exact rowEval19116 x
  · exact rowEval19117 x
  · exact rowEval19118 x

theorem entryEval7_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_1 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck7_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_1]

def rows7_2 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19119, row19120, row19121, row19122, row19123, row19124, row19125, row19126, row19127, row19128, row19129, row19130, row19131, row19132, row19133, row19134, row19135, row19136, row19137, row19138]

theorem entryCheck7_2 : entry7_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_2 k)) := by decide +kernel

theorem rowsSound7_2 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval19119 x
  · exact rowEval19120 x
  · exact rowEval19121 x
  · exact rowEval19122 x
  · exact rowEval19123 x
  · exact rowEval19124 x
  · exact rowEval19125 x
  · exact rowEval19126 x
  · exact rowEval19127 x
  · exact rowEval19128 x
  · exact rowEval19129 x
  · exact rowEval19130 x
  · exact rowEval19131 x
  · exact rowEval19132 x
  · exact rowEval19133 x
  · exact rowEval19134 x
  · exact rowEval19135 x
  · exact rowEval19136 x
  · exact rowEval19137 x
  · exact rowEval19138 x

theorem entryEval7_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_2 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck7_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_2]

def rows7_3 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19139, row19140, row19141, row19142, row19143, row19144, row19145, row19146, row19147, row19148, row19149, row19150, row19151, row19152, row19153, row19154, row19155, row19156, row19157, row19158]

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19139 x
  · exact rowEval19140 x
  · exact rowEval19141 x
  · exact rowEval19142 x
  · exact rowEval19143 x
  · exact rowEval19144 x
  · exact rowEval19145 x
  · exact rowEval19146 x
  · exact rowEval19147 x
  · exact rowEval19148 x
  · exact rowEval19149 x
  · exact rowEval19150 x
  · exact rowEval19151 x
  · exact rowEval19152 x
  · exact rowEval19153 x
  · exact rowEval19154 x
  · exact rowEval19155 x
  · exact rowEval19156 x
  · exact rowEval19157 x
  · exact rowEval19158 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

def rows7_4 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19159, row19160, row19161, row19162, row19163, row19164, row19165, row19166, row19167, row19168, row19169, row19170, row19171, row19172, row19173, row19174, row19175, row19176, row19177, row19178]

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19159 x
  · exact rowEval19160 x
  · exact rowEval19161 x
  · exact rowEval19162 x
  · exact rowEval19163 x
  · exact rowEval19164 x
  · exact rowEval19165 x
  · exact rowEval19166 x
  · exact rowEval19167 x
  · exact rowEval19168 x
  · exact rowEval19169 x
  · exact rowEval19170 x
  · exact rowEval19171 x
  · exact rowEval19172 x
  · exact rowEval19173 x
  · exact rowEval19174 x
  · exact rowEval19175 x
  · exact rowEval19176 x
  · exact rowEval19177 x
  · exact rowEval19178 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

def rows7_5 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19179, row19180, row19181, row19182, row19183, row19184, row19185, row19186, row19187, row19188, row19189, row19190, row19191, row19192, row19193, row19194, row19195, row19196, row19197, row19198]

theorem entryCheck7_5 : entry7_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_5 k)) := by decide +kernel

theorem rowsSound7_5 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19179 x
  · exact rowEval19180 x
  · exact rowEval19181 x
  · exact rowEval19182 x
  · exact rowEval19183 x
  · exact rowEval19184 x
  · exact rowEval19185 x
  · exact rowEval19186 x
  · exact rowEval19187 x
  · exact rowEval19188 x
  · exact rowEval19189 x
  · exact rowEval19190 x
  · exact rowEval19191 x
  · exact rowEval19192 x
  · exact rowEval19193 x
  · exact rowEval19194 x
  · exact rowEval19195 x
  · exact rowEval19196 x
  · exact rowEval19197 x
  · exact rowEval19198 x

theorem entryEval7_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_5 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck7_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_5]

def rows7_6 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19199, row19200, row19201, row19202, row19203, row19204, row19205, row19206, row19207, row19208, row19209, row19210, row19211, row19212, row19213, row19214, row19215, row19216, row19217, row19218]

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19199 x
  · exact rowEval19200 x
  · exact rowEval19201 x
  · exact rowEval19202 x
  · exact rowEval19203 x
  · exact rowEval19204 x
  · exact rowEval19205 x
  · exact rowEval19206 x
  · exact rowEval19207 x
  · exact rowEval19208 x
  · exact rowEval19209 x
  · exact rowEval19210 x
  · exact rowEval19211 x
  · exact rowEval19212 x
  · exact rowEval19213 x
  · exact rowEval19214 x
  · exact rowEval19215 x
  · exact rowEval19216 x
  · exact rowEval19217 x
  · exact rowEval19218 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

def rows7_7 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19219, row19220, row19221, row19222, row19223, row19224, row19225, row19226, row19227, row19228, row19229, row19230, row19231, row19232, row19233, row19234, row19235, row19236, row19237, row19238]

theorem entryCheck7_7 : entry7_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_7 k)) := by decide +kernel

theorem rowsSound7_7 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval19219 x
  · exact rowEval19220 x
  · exact rowEval19221 x
  · exact rowEval19222 x
  · exact rowEval19223 x
  · exact rowEval19224 x
  · exact rowEval19225 x
  · exact rowEval19226 x
  · exact rowEval19227 x
  · exact rowEval19228 x
  · exact rowEval19229 x
  · exact rowEval19230 x
  · exact rowEval19231 x
  · exact rowEval19232 x
  · exact rowEval19233 x
  · exact rowEval19234 x
  · exact rowEval19235 x
  · exact rowEval19236 x
  · exact rowEval19237 x
  · exact rowEval19238 x

theorem entryEval7_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_7 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck7_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_7]

end MUB6.Certificate.GramEntries.Block5

end OAI
