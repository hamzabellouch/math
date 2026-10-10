import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramRows.Block0
import OAI.Analysis.MutuallyUnbiased.GramRows.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block4

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block0.form2.size → Integer.Sparse Key := ![row126, row127, row128, row129, row130, row131, row132, row133, row134, row135, row136, row137, row138, row139, row140, row141, row142, row143, row144, row145, row146, row147, row148, row149, row150, row151, row152, row153, row154, row155, row156, row157, row158, row159, row160, row161, row162, row163, row164, row165, row166, row167]

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block0.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form2.terms k).tag (GramFunctions.Block0.form2.terms k).charge GramFunctions.Block0.form0) x := by
  fin_cases k
  · exact rowEval126 x
  · exact rowEval127 x
  · exact rowEval128 x
  · exact rowEval129 x
  · exact rowEval130 x
  · exact rowEval131 x
  · exact rowEval132 x
  · exact rowEval133 x
  · exact rowEval134 x
  · exact rowEval135 x
  · exact rowEval136 x
  · exact rowEval137 x
  · exact rowEval138 x
  · exact rowEval139 x
  · exact rowEval140 x
  · exact rowEval141 x
  · exact rowEval142 x
  · exact rowEval143 x
  · exact rowEval144 x
  · exact rowEval145 x
  · exact rowEval146 x
  · exact rowEval147 x
  · exact rowEval148 x
  · exact rowEval149 x
  · exact rowEval150 x
  · exact rowEval151 x
  · exact rowEval152 x
  · exact rowEval153 x
  · exact rowEval154 x
  · exact rowEval155 x
  · exact rowEval156 x
  · exact rowEval157 x
  · exact rowEval158 x
  · exact rowEval159 x
  · exact rowEval160 x
  · exact rowEval161 x
  · exact rowEval162 x
  · exact rowEval163 x
  · exact rowEval164 x
  · exact rowEval165 x
  · exact rowEval166 x
  · exact rowEval167 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block0.form2.mixedGram GramFunctions.Block0.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form2 GramFunctions.Block0.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

def rows2_1 : Fin GramFunctions.Block0.form2.size → Integer.Sparse Key := ![row168, row169, row170, row171, row172, row173, row174, row175, row176, row177, row178, row179, row180, row181, row182, row183, row184, row185, row186, row187, row188, row189, row190, row191, row192, row193, row194, row195, row196, row197, row198, row199, row200, row201, row202, row203, row204, row205, row206, row207, row208, row209]

theorem entryCheck2_1 : entry2_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form2.terms k).coefficient) (rows2_1 k)) := by decide +kernel

theorem rowsSound2_1 (k : Fin GramFunctions.Block0.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form2.terms k).tag (GramFunctions.Block0.form2.terms k).charge GramFunctions.Block0.form1) x := by
  fin_cases k
  · exact rowEval168 x
  · exact rowEval169 x
  · exact rowEval170 x
  · exact rowEval171 x
  · exact rowEval172 x
  · exact rowEval173 x
  · exact rowEval174 x
  · exact rowEval175 x
  · exact rowEval176 x
  · exact rowEval177 x
  · exact rowEval178 x
  · exact rowEval179 x
  · exact rowEval180 x
  · exact rowEval181 x
  · exact rowEval182 x
  · exact rowEval183 x
  · exact rowEval184 x
  · exact rowEval185 x
  · exact rowEval186 x
  · exact rowEval187 x
  · exact rowEval188 x
  · exact rowEval189 x
  · exact rowEval190 x
  · exact rowEval191 x
  · exact rowEval192 x
  · exact rowEval193 x
  · exact rowEval194 x
  · exact rowEval195 x
  · exact rowEval196 x
  · exact rowEval197 x
  · exact rowEval198 x
  · exact rowEval199 x
  · exact rowEval200 x
  · exact rowEval201 x
  · exact rowEval202 x
  · exact rowEval203 x
  · exact rowEval204 x
  · exact rowEval205 x
  · exact rowEval206 x
  · exact rowEval207 x
  · exact rowEval208 x
  · exact rowEval209 x

theorem entryEval2_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_1 (GramNormalization.eval B) = GramFunctions.Block0.form2.mixedGram GramFunctions.Block0.form1 B := by
  rw [entryCheck2_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form2 GramFunctions.Block0.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_1]

def rows2_2 : Fin GramFunctions.Block0.form2.size → Integer.Sparse Key := ![row210, row211, row212, row213, row214, row215, row216, row217, row218, row219, row220, row221, row222, row223, row224, row225, row226, row227, row228, row229, row230, row231, row232, row233, row234, row235, row236, row237, row238, row239, row240, row241, row242, row243, row244, row245, row246, row247, row248, row249, row250, row251]

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block0.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form2.terms k).tag (GramFunctions.Block0.form2.terms k).charge GramFunctions.Block0.form2) x := by
  fin_cases k
  · exact rowEval210 x
  · exact rowEval211 x
  · exact rowEval212 x
  · exact rowEval213 x
  · exact rowEval214 x
  · exact rowEval215 x
  · exact rowEval216 x
  · exact rowEval217 x
  · exact rowEval218 x
  · exact rowEval219 x
  · exact rowEval220 x
  · exact rowEval221 x
  · exact rowEval222 x
  · exact rowEval223 x
  · exact rowEval224 x
  · exact rowEval225 x
  · exact rowEval226 x
  · exact rowEval227 x
  · exact rowEval228 x
  · exact rowEval229 x
  · exact rowEval230 x
  · exact rowEval231 x
  · exact rowEval232 x
  · exact rowEval233 x
  · exact rowEval234 x
  · exact rowEval235 x
  · exact rowEval236 x
  · exact rowEval237 x
  · exact rowEval238 x
  · exact rowEval239 x
  · exact rowEval240 x
  · exact rowEval241 x
  · exact rowEval242 x
  · exact rowEval243 x
  · exact rowEval244 x
  · exact rowEval245 x
  · exact rowEval246 x
  · exact rowEval247 x
  · exact rowEval248 x
  · exact rowEval249 x
  · exact rowEval250 x
  · exact rowEval251 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block0.form2.mixedGram GramFunctions.Block0.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form2 GramFunctions.Block0.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

end MUB6.Certificate.GramEntries.Block0

end OAI
