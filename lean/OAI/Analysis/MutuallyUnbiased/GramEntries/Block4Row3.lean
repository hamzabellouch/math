import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block127
import OAI.Analysis.MutuallyUnbiased.GramRows.Block128

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13305, row13306, row13307, row13308, row13309, row13310, row13311, row13312, row13313, row13314, row13315, row13316, row13317, row13318, row13319, row13320, row13321, row13322, row13323, row13324]

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block4.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form3.terms k).tag (GramFunctions.Block4.form3.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13305 x
  · exact rowEval13306 x
  · exact rowEval13307 x
  · exact rowEval13308 x
  · exact rowEval13309 x
  · exact rowEval13310 x
  · exact rowEval13311 x
  · exact rowEval13312 x
  · exact rowEval13313 x
  · exact rowEval13314 x
  · exact rowEval13315 x
  · exact rowEval13316 x
  · exact rowEval13317 x
  · exact rowEval13318 x
  · exact rowEval13319 x
  · exact rowEval13320 x
  · exact rowEval13321 x
  · exact rowEval13322 x
  · exact rowEval13323 x
  · exact rowEval13324 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block4.form3.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form3 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

def rows3_1 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13325, row13326, row13327, row13328, row13329, row13330, row13331, row13332, row13333, row13334, row13335, row13336, row13337, row13338, row13339, row13340, row13341, row13342, row13343, row13344]

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block4.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form3.terms k).tag (GramFunctions.Block4.form3.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13325 x
  · exact rowEval13326 x
  · exact rowEval13327 x
  · exact rowEval13328 x
  · exact rowEval13329 x
  · exact rowEval13330 x
  · exact rowEval13331 x
  · exact rowEval13332 x
  · exact rowEval13333 x
  · exact rowEval13334 x
  · exact rowEval13335 x
  · exact rowEval13336 x
  · exact rowEval13337 x
  · exact rowEval13338 x
  · exact rowEval13339 x
  · exact rowEval13340 x
  · exact rowEval13341 x
  · exact rowEval13342 x
  · exact rowEval13343 x
  · exact rowEval13344 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block4.form3.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form3 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

def rows3_2 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13345, row13346, row13347, row13348, row13349, row13350, row13351, row13352, row13353, row13354, row13355, row13356, row13357, row13358, row13359, row13360, row13361, row13362, row13363, row13364]

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block4.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form3.terms k).tag (GramFunctions.Block4.form3.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13345 x
  · exact rowEval13346 x
  · exact rowEval13347 x
  · exact rowEval13348 x
  · exact rowEval13349 x
  · exact rowEval13350 x
  · exact rowEval13351 x
  · exact rowEval13352 x
  · exact rowEval13353 x
  · exact rowEval13354 x
  · exact rowEval13355 x
  · exact rowEval13356 x
  · exact rowEval13357 x
  · exact rowEval13358 x
  · exact rowEval13359 x
  · exact rowEval13360 x
  · exact rowEval13361 x
  · exact rowEval13362 x
  · exact rowEval13363 x
  · exact rowEval13364 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block4.form3.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form3 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

def rows3_3 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13365, row13366, row13367, row13368, row13369, row13370, row13371, row13372, row13373, row13374, row13375, row13376, row13377, row13378, row13379, row13380, row13381, row13382, row13383, row13384]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block4.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form3.terms k).tag (GramFunctions.Block4.form3.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13365 x
  · exact rowEval13366 x
  · exact rowEval13367 x
  · exact rowEval13368 x
  · exact rowEval13369 x
  · exact rowEval13370 x
  · exact rowEval13371 x
  · exact rowEval13372 x
  · exact rowEval13373 x
  · exact rowEval13374 x
  · exact rowEval13375 x
  · exact rowEval13376 x
  · exact rowEval13377 x
  · exact rowEval13378 x
  · exact rowEval13379 x
  · exact rowEval13380 x
  · exact rowEval13381 x
  · exact rowEval13382 x
  · exact rowEval13383 x
  · exact rowEval13384 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block4.form3.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form3 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block4

end OAI
