import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block128
import OAI.Analysis.MutuallyUnbiased.GramRows.Block129

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13385, row13386, row13387, row13388, row13389, row13390, row13391, row13392, row13393, row13394, row13395, row13396, row13397, row13398, row13399, row13400, row13401, row13402, row13403, row13404]

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13385 x
  · exact rowEval13386 x
  · exact rowEval13387 x
  · exact rowEval13388 x
  · exact rowEval13389 x
  · exact rowEval13390 x
  · exact rowEval13391 x
  · exact rowEval13392 x
  · exact rowEval13393 x
  · exact rowEval13394 x
  · exact rowEval13395 x
  · exact rowEval13396 x
  · exact rowEval13397 x
  · exact rowEval13398 x
  · exact rowEval13399 x
  · exact rowEval13400 x
  · exact rowEval13401 x
  · exact rowEval13402 x
  · exact rowEval13403 x
  · exact rowEval13404 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

def rows4_1 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13405, row13406, row13407, row13408, row13409, row13410, row13411, row13412, row13413, row13414, row13415, row13416, row13417, row13418, row13419, row13420, row13421, row13422, row13423, row13424]

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13405 x
  · exact rowEval13406 x
  · exact rowEval13407 x
  · exact rowEval13408 x
  · exact rowEval13409 x
  · exact rowEval13410 x
  · exact rowEval13411 x
  · exact rowEval13412 x
  · exact rowEval13413 x
  · exact rowEval13414 x
  · exact rowEval13415 x
  · exact rowEval13416 x
  · exact rowEval13417 x
  · exact rowEval13418 x
  · exact rowEval13419 x
  · exact rowEval13420 x
  · exact rowEval13421 x
  · exact rowEval13422 x
  · exact rowEval13423 x
  · exact rowEval13424 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

def rows4_2 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13425, row13426, row13427, row13428, row13429, row13430, row13431, row13432, row13433, row13434, row13435, row13436, row13437, row13438, row13439, row13440, row13441, row13442, row13443, row13444]

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13425 x
  · exact rowEval13426 x
  · exact rowEval13427 x
  · exact rowEval13428 x
  · exact rowEval13429 x
  · exact rowEval13430 x
  · exact rowEval13431 x
  · exact rowEval13432 x
  · exact rowEval13433 x
  · exact rowEval13434 x
  · exact rowEval13435 x
  · exact rowEval13436 x
  · exact rowEval13437 x
  · exact rowEval13438 x
  · exact rowEval13439 x
  · exact rowEval13440 x
  · exact rowEval13441 x
  · exact rowEval13442 x
  · exact rowEval13443 x
  · exact rowEval13444 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

def rows4_3 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13445, row13446, row13447, row13448, row13449, row13450, row13451, row13452, row13453, row13454, row13455, row13456, row13457, row13458, row13459, row13460, row13461, row13462, row13463, row13464]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13445 x
  · exact rowEval13446 x
  · exact rowEval13447 x
  · exact rowEval13448 x
  · exact rowEval13449 x
  · exact rowEval13450 x
  · exact rowEval13451 x
  · exact rowEval13452 x
  · exact rowEval13453 x
  · exact rowEval13454 x
  · exact rowEval13455 x
  · exact rowEval13456 x
  · exact rowEval13457 x
  · exact rowEval13458 x
  · exact rowEval13459 x
  · exact rowEval13460 x
  · exact rowEval13461 x
  · exact rowEval13462 x
  · exact rowEval13463 x
  · exact rowEval13464 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

def rows4_4 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13465, row13466, row13467, row13468, row13469, row13470, row13471, row13472, row13473, row13474, row13475, row13476, row13477, row13478, row13479, row13480, row13481, row13482, row13483, row13484]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval13465 x
  · exact rowEval13466 x
  · exact rowEval13467 x
  · exact rowEval13468 x
  · exact rowEval13469 x
  · exact rowEval13470 x
  · exact rowEval13471 x
  · exact rowEval13472 x
  · exact rowEval13473 x
  · exact rowEval13474 x
  · exact rowEval13475 x
  · exact rowEval13476 x
  · exact rowEval13477 x
  · exact rowEval13478 x
  · exact rowEval13479 x
  · exact rowEval13480 x
  · exact rowEval13481 x
  · exact rowEval13482 x
  · exact rowEval13483 x
  · exact rowEval13484 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block4

end OAI
