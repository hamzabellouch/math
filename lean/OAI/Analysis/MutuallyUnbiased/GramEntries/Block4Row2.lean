import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block127

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block4.form2.size → Integer.Sparse Key := ![row13245, row13246, row13247, row13248, row13249, row13250, row13251, row13252, row13253, row13254, row13255, row13256, row13257, row13258, row13259, row13260, row13261, row13262, row13263, row13264]

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block4.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form2.terms k).tag (GramFunctions.Block4.form2.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13245 x
  · exact rowEval13246 x
  · exact rowEval13247 x
  · exact rowEval13248 x
  · exact rowEval13249 x
  · exact rowEval13250 x
  · exact rowEval13251 x
  · exact rowEval13252 x
  · exact rowEval13253 x
  · exact rowEval13254 x
  · exact rowEval13255 x
  · exact rowEval13256 x
  · exact rowEval13257 x
  · exact rowEval13258 x
  · exact rowEval13259 x
  · exact rowEval13260 x
  · exact rowEval13261 x
  · exact rowEval13262 x
  · exact rowEval13263 x
  · exact rowEval13264 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block4.form2.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form2 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

def rows2_1 : Fin GramFunctions.Block4.form2.size → Integer.Sparse Key := ![row13265, row13266, row13267, row13268, row13269, row13270, row13271, row13272, row13273, row13274, row13275, row13276, row13277, row13278, row13279, row13280, row13281, row13282, row13283, row13284]

theorem entryCheck2_1 : entry2_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form2.terms k).coefficient) (rows2_1 k)) := by decide +kernel

theorem rowsSound2_1 (k : Fin GramFunctions.Block4.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form2.terms k).tag (GramFunctions.Block4.form2.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13265 x
  · exact rowEval13266 x
  · exact rowEval13267 x
  · exact rowEval13268 x
  · exact rowEval13269 x
  · exact rowEval13270 x
  · exact rowEval13271 x
  · exact rowEval13272 x
  · exact rowEval13273 x
  · exact rowEval13274 x
  · exact rowEval13275 x
  · exact rowEval13276 x
  · exact rowEval13277 x
  · exact rowEval13278 x
  · exact rowEval13279 x
  · exact rowEval13280 x
  · exact rowEval13281 x
  · exact rowEval13282 x
  · exact rowEval13283 x
  · exact rowEval13284 x

theorem entryEval2_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_1 (GramNormalization.eval B) = GramFunctions.Block4.form2.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck2_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form2 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_1]

def rows2_2 : Fin GramFunctions.Block4.form2.size → Integer.Sparse Key := ![row13285, row13286, row13287, row13288, row13289, row13290, row13291, row13292, row13293, row13294, row13295, row13296, row13297, row13298, row13299, row13300, row13301, row13302, row13303, row13304]

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block4.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form2.terms k).tag (GramFunctions.Block4.form2.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13285 x
  · exact rowEval13286 x
  · exact rowEval13287 x
  · exact rowEval13288 x
  · exact rowEval13289 x
  · exact rowEval13290 x
  · exact rowEval13291 x
  · exact rowEval13292 x
  · exact rowEval13293 x
  · exact rowEval13294 x
  · exact rowEval13295 x
  · exact rowEval13296 x
  · exact rowEval13297 x
  · exact rowEval13298 x
  · exact rowEval13299 x
  · exact rowEval13300 x
  · exact rowEval13301 x
  · exact rowEval13302 x
  · exact rowEval13303 x
  · exact rowEval13304 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block4.form2.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form2 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

end MUB6.Certificate.GramEntries.Block4

end OAI
