import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block160
import OAI.Analysis.MutuallyUnbiased.GramRows.Block161

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows19_0 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17411, row17412, row17413, row17414, row17415, row17416, row17417, row17418, row17419, row17420]

theorem entryCheck19_0 : entry19_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_0 k)) := by decide +kernel

theorem rowsSound19_0 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17411 x
  · exact rowEval17412 x
  · exact rowEval17413 x
  · exact rowEval17414 x
  · exact rowEval17415 x
  · exact rowEval17416 x
  · exact rowEval17417 x
  · exact rowEval17418 x
  · exact rowEval17419 x
  · exact rowEval17420 x

theorem entryEval19_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_0 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck19_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_0]

def rows19_1 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17421, row17422, row17423, row17424, row17425, row17426, row17427, row17428, row17429, row17430]

theorem entryCheck19_1 : entry19_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_1 k)) := by decide +kernel

theorem rowsSound19_1 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval17421 x
  · exact rowEval17422 x
  · exact rowEval17423 x
  · exact rowEval17424 x
  · exact rowEval17425 x
  · exact rowEval17426 x
  · exact rowEval17427 x
  · exact rowEval17428 x
  · exact rowEval17429 x
  · exact rowEval17430 x

theorem entryEval19_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_1 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck19_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_1]

def rows19_2 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17431, row17432, row17433, row17434, row17435, row17436, row17437, row17438, row17439, row17440]

theorem entryCheck19_2 : entry19_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_2 k)) := by decide +kernel

theorem rowsSound19_2 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval17431 x
  · exact rowEval17432 x
  · exact rowEval17433 x
  · exact rowEval17434 x
  · exact rowEval17435 x
  · exact rowEval17436 x
  · exact rowEval17437 x
  · exact rowEval17438 x
  · exact rowEval17439 x
  · exact rowEval17440 x

theorem entryEval19_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_2 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck19_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_2]

def rows19_3 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17441, row17442, row17443, row17444, row17445, row17446, row17447, row17448, row17449, row17450]

theorem entryCheck19_3 : entry19_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_3 k)) := by decide +kernel

theorem rowsSound19_3 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval17441 x
  · exact rowEval17442 x
  · exact rowEval17443 x
  · exact rowEval17444 x
  · exact rowEval17445 x
  · exact rowEval17446 x
  · exact rowEval17447 x
  · exact rowEval17448 x
  · exact rowEval17449 x
  · exact rowEval17450 x

theorem entryEval19_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_3 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck19_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_3]

def rows19_4 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17451, row17452, row17453, row17454, row17455, row17456, row17457, row17458, row17459, row17460]

theorem entryCheck19_4 : entry19_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_4 k)) := by decide +kernel

theorem rowsSound19_4 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval17451 x
  · exact rowEval17452 x
  · exact rowEval17453 x
  · exact rowEval17454 x
  · exact rowEval17455 x
  · exact rowEval17456 x
  · exact rowEval17457 x
  · exact rowEval17458 x
  · exact rowEval17459 x
  · exact rowEval17460 x

theorem entryEval19_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_4 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck19_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_4]

def rows19_5 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17461, row17462, row17463, row17464, row17465, row17466, row17467, row17468, row17469, row17470]

theorem entryCheck19_5 : entry19_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_5 k)) := by decide +kernel

theorem rowsSound19_5 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval17461 x
  · exact rowEval17462 x
  · exact rowEval17463 x
  · exact rowEval17464 x
  · exact rowEval17465 x
  · exact rowEval17466 x
  · exact rowEval17467 x
  · exact rowEval17468 x
  · exact rowEval17469 x
  · exact rowEval17470 x

theorem entryEval19_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_5 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck19_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_5]

def rows19_6 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17471, row17472, row17473, row17474, row17475, row17476, row17477, row17478, row17479, row17480]

theorem entryCheck19_6 : entry19_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_6 k)) := by decide +kernel

theorem rowsSound19_6 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval17471 x
  · exact rowEval17472 x
  · exact rowEval17473 x
  · exact rowEval17474 x
  · exact rowEval17475 x
  · exact rowEval17476 x
  · exact rowEval17477 x
  · exact rowEval17478 x
  · exact rowEval17479 x
  · exact rowEval17480 x

theorem entryEval19_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_6 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck19_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_6]

def rows19_7 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17481, row17482, row17483, row17484, row17485, row17486, row17487, row17488, row17489, row17490]

theorem entryCheck19_7 : entry19_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_7 k)) := by decide +kernel

theorem rowsSound19_7 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval17481 x
  · exact rowEval17482 x
  · exact rowEval17483 x
  · exact rowEval17484 x
  · exact rowEval17485 x
  · exact rowEval17486 x
  · exact rowEval17487 x
  · exact rowEval17488 x
  · exact rowEval17489 x
  · exact rowEval17490 x

theorem entryEval19_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_7 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck19_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_7]

def rows19_8 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17491, row17492, row17493, row17494, row17495, row17496, row17497, row17498, row17499, row17500]

theorem entryCheck19_8 : entry19_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_8 k)) := by decide +kernel

theorem rowsSound19_8 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval17491 x
  · exact rowEval17492 x
  · exact rowEval17493 x
  · exact rowEval17494 x
  · exact rowEval17495 x
  · exact rowEval17496 x
  · exact rowEval17497 x
  · exact rowEval17498 x
  · exact rowEval17499 x
  · exact rowEval17500 x

theorem entryEval19_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_8 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck19_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_8]

def rows19_9 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17501, row17502, row17503, row17504, row17505, row17506, row17507, row17508, row17509, row17510]

theorem entryCheck19_9 : entry19_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_9 k)) := by decide +kernel

theorem rowsSound19_9 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval17501 x
  · exact rowEval17502 x
  · exact rowEval17503 x
  · exact rowEval17504 x
  · exact rowEval17505 x
  · exact rowEval17506 x
  · exact rowEval17507 x
  · exact rowEval17508 x
  · exact rowEval17509 x
  · exact rowEval17510 x

theorem entryEval19_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_9 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck19_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_9]

def rows19_10 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17511, row17512, row17513, row17514, row17515, row17516, row17517, row17518, row17519, row17520]

theorem entryCheck19_10 : entry19_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_10 k)) := by decide +kernel

theorem rowsSound19_10 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval17511 x
  · exact rowEval17512 x
  · exact rowEval17513 x
  · exact rowEval17514 x
  · exact rowEval17515 x
  · exact rowEval17516 x
  · exact rowEval17517 x
  · exact rowEval17518 x
  · exact rowEval17519 x
  · exact rowEval17520 x

theorem entryEval19_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_10 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck19_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_10]

def rows19_11 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17521, row17522, row17523, row17524, row17525, row17526, row17527, row17528, row17529, row17530]

theorem entryCheck19_11 : entry19_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_11 k)) := by decide +kernel

theorem rowsSound19_11 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval17521 x
  · exact rowEval17522 x
  · exact rowEval17523 x
  · exact rowEval17524 x
  · exact rowEval17525 x
  · exact rowEval17526 x
  · exact rowEval17527 x
  · exact rowEval17528 x
  · exact rowEval17529 x
  · exact rowEval17530 x

theorem entryEval19_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_11 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck19_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_11]

def rows19_12 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17531, row17532, row17533, row17534, row17535, row17536, row17537, row17538, row17539, row17540]

theorem entryCheck19_12 : entry19_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_12 k)) := by decide +kernel

theorem rowsSound19_12 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval17531 x
  · exact rowEval17532 x
  · exact rowEval17533 x
  · exact rowEval17534 x
  · exact rowEval17535 x
  · exact rowEval17536 x
  · exact rowEval17537 x
  · exact rowEval17538 x
  · exact rowEval17539 x
  · exact rowEval17540 x

theorem entryEval19_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_12 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck19_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_12]

def rows19_13 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17541, row17542, row17543, row17544, row17545, row17546, row17547, row17548, row17549, row17550]

theorem entryCheck19_13 : entry19_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_13 k)) := by decide +kernel

theorem rowsSound19_13 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval17541 x
  · exact rowEval17542 x
  · exact rowEval17543 x
  · exact rowEval17544 x
  · exact rowEval17545 x
  · exact rowEval17546 x
  · exact rowEval17547 x
  · exact rowEval17548 x
  · exact rowEval17549 x
  · exact rowEval17550 x

theorem entryEval19_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_13 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck19_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_13]

def rows19_14 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17551, row17552, row17553, row17554, row17555, row17556, row17557, row17558, row17559, row17560]

theorem entryCheck19_14 : entry19_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_14 k)) := by decide +kernel

theorem rowsSound19_14 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form14) x := by
  fin_cases k
  · exact rowEval17551 x
  · exact rowEval17552 x
  · exact rowEval17553 x
  · exact rowEval17554 x
  · exact rowEval17555 x
  · exact rowEval17556 x
  · exact rowEval17557 x
  · exact rowEval17558 x
  · exact rowEval17559 x
  · exact rowEval17560 x

theorem entryEval19_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_14 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form14 B := by
  rw [entryCheck19_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_14]

def rows19_15 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17561, row17562, row17563, row17564, row17565, row17566, row17567, row17568, row17569, row17570]

theorem entryCheck19_15 : entry19_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_15 k)) := by decide +kernel

theorem rowsSound19_15 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form15) x := by
  fin_cases k
  · exact rowEval17561 x
  · exact rowEval17562 x
  · exact rowEval17563 x
  · exact rowEval17564 x
  · exact rowEval17565 x
  · exact rowEval17566 x
  · exact rowEval17567 x
  · exact rowEval17568 x
  · exact rowEval17569 x
  · exact rowEval17570 x

theorem entryEval19_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_15 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form15 B := by
  rw [entryCheck19_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_15]

def rows19_16 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17571, row17572, row17573, row17574, row17575, row17576, row17577, row17578, row17579, row17580]

theorem entryCheck19_16 : entry19_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_16 k)) := by decide +kernel

theorem rowsSound19_16 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form16) x := by
  fin_cases k
  · exact rowEval17571 x
  · exact rowEval17572 x
  · exact rowEval17573 x
  · exact rowEval17574 x
  · exact rowEval17575 x
  · exact rowEval17576 x
  · exact rowEval17577 x
  · exact rowEval17578 x
  · exact rowEval17579 x
  · exact rowEval17580 x

theorem entryEval19_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_16 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form16 B := by
  rw [entryCheck19_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_16]

def rows19_17 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17581, row17582, row17583, row17584, row17585, row17586, row17587, row17588, row17589, row17590]

theorem entryCheck19_17 : entry19_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_17 k)) := by decide +kernel

theorem rowsSound19_17 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval17581 x
  · exact rowEval17582 x
  · exact rowEval17583 x
  · exact rowEval17584 x
  · exact rowEval17585 x
  · exact rowEval17586 x
  · exact rowEval17587 x
  · exact rowEval17588 x
  · exact rowEval17589 x
  · exact rowEval17590 x

theorem entryEval19_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_17 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck19_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_17]

def rows19_18 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17591, row17592, row17593, row17594, row17595, row17596, row17597, row17598, row17599, row17600]

theorem entryCheck19_18 : entry19_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_18 k)) := by decide +kernel

theorem rowsSound19_18 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form18) x := by
  fin_cases k
  · exact rowEval17591 x
  · exact rowEval17592 x
  · exact rowEval17593 x
  · exact rowEval17594 x
  · exact rowEval17595 x
  · exact rowEval17596 x
  · exact rowEval17597 x
  · exact rowEval17598 x
  · exact rowEval17599 x
  · exact rowEval17600 x

theorem entryEval19_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_18 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form18 B := by
  rw [entryCheck19_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_18]

def rows19_19 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17601, row17602, row17603, row17604, row17605, row17606, row17607, row17608, row17609, row17610]

theorem entryCheck19_19 : entry19_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_19 k)) := by decide +kernel

theorem rowsSound19_19 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form19) x := by
  fin_cases k
  · exact rowEval17601 x
  · exact rowEval17602 x
  · exact rowEval17603 x
  · exact rowEval17604 x
  · exact rowEval17605 x
  · exact rowEval17606 x
  · exact rowEval17607 x
  · exact rowEval17608 x
  · exact rowEval17609 x
  · exact rowEval17610 x

theorem entryEval19_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_19 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form19 B := by
  rw [entryCheck19_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_19]

end MUB6.Certificate.GramEntries.Block4

end OAI
