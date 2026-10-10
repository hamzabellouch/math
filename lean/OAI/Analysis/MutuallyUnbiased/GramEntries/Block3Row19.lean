import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block105
import OAI.Analysis.MutuallyUnbiased.GramRows.Block106

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows19_0 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10389, row10390, row10391, row10392, row10393, row10394, row10395, row10396, row10397, row10398]

theorem entryCheck19_0 : entry19_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_0 k)) := by decide +kernel

theorem rowsSound19_0 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval10389 x
  · exact rowEval10390 x
  · exact rowEval10391 x
  · exact rowEval10392 x
  · exact rowEval10393 x
  · exact rowEval10394 x
  · exact rowEval10395 x
  · exact rowEval10396 x
  · exact rowEval10397 x
  · exact rowEval10398 x

theorem entryEval19_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_0 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck19_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_0]

def rows19_1 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10399, row10400, row10401, row10402, row10403, row10404, row10405, row10406, row10407, row10408]

theorem entryCheck19_1 : entry19_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_1 k)) := by decide +kernel

theorem rowsSound19_1 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval10399 x
  · exact rowEval10400 x
  · exact rowEval10401 x
  · exact rowEval10402 x
  · exact rowEval10403 x
  · exact rowEval10404 x
  · exact rowEval10405 x
  · exact rowEval10406 x
  · exact rowEval10407 x
  · exact rowEval10408 x

theorem entryEval19_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_1 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck19_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_1]

def rows19_2 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10409, row10410, row10411, row10412, row10413, row10414, row10415, row10416, row10417, row10418]

theorem entryCheck19_2 : entry19_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_2 k)) := by decide +kernel

theorem rowsSound19_2 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval10409 x
  · exact rowEval10410 x
  · exact rowEval10411 x
  · exact rowEval10412 x
  · exact rowEval10413 x
  · exact rowEval10414 x
  · exact rowEval10415 x
  · exact rowEval10416 x
  · exact rowEval10417 x
  · exact rowEval10418 x

theorem entryEval19_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_2 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck19_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_2]

def rows19_3 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10419, row10420, row10421, row10422, row10423, row10424, row10425, row10426, row10427, row10428]

theorem entryCheck19_3 : entry19_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_3 k)) := by decide +kernel

theorem rowsSound19_3 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval10419 x
  · exact rowEval10420 x
  · exact rowEval10421 x
  · exact rowEval10422 x
  · exact rowEval10423 x
  · exact rowEval10424 x
  · exact rowEval10425 x
  · exact rowEval10426 x
  · exact rowEval10427 x
  · exact rowEval10428 x

theorem entryEval19_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_3 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck19_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_3]

def rows19_4 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10429, row10430, row10431, row10432, row10433, row10434, row10435, row10436, row10437, row10438]

theorem entryCheck19_4 : entry19_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_4 k)) := by decide +kernel

theorem rowsSound19_4 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval10429 x
  · exact rowEval10430 x
  · exact rowEval10431 x
  · exact rowEval10432 x
  · exact rowEval10433 x
  · exact rowEval10434 x
  · exact rowEval10435 x
  · exact rowEval10436 x
  · exact rowEval10437 x
  · exact rowEval10438 x

theorem entryEval19_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_4 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck19_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_4]

def rows19_5 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10439, row10440, row10441, row10442, row10443, row10444, row10445, row10446, row10447, row10448]

theorem entryCheck19_5 : entry19_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_5 k)) := by decide +kernel

theorem rowsSound19_5 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval10439 x
  · exact rowEval10440 x
  · exact rowEval10441 x
  · exact rowEval10442 x
  · exact rowEval10443 x
  · exact rowEval10444 x
  · exact rowEval10445 x
  · exact rowEval10446 x
  · exact rowEval10447 x
  · exact rowEval10448 x

theorem entryEval19_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_5 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck19_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_5]

def rows19_6 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10449, row10450, row10451, row10452, row10453, row10454, row10455, row10456, row10457, row10458]

theorem entryCheck19_6 : entry19_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_6 k)) := by decide +kernel

theorem rowsSound19_6 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval10449 x
  · exact rowEval10450 x
  · exact rowEval10451 x
  · exact rowEval10452 x
  · exact rowEval10453 x
  · exact rowEval10454 x
  · exact rowEval10455 x
  · exact rowEval10456 x
  · exact rowEval10457 x
  · exact rowEval10458 x

theorem entryEval19_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_6 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck19_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_6]

def rows19_7 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10459, row10460, row10461, row10462, row10463, row10464, row10465, row10466, row10467, row10468]

theorem entryCheck19_7 : entry19_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_7 k)) := by decide +kernel

theorem rowsSound19_7 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval10459 x
  · exact rowEval10460 x
  · exact rowEval10461 x
  · exact rowEval10462 x
  · exact rowEval10463 x
  · exact rowEval10464 x
  · exact rowEval10465 x
  · exact rowEval10466 x
  · exact rowEval10467 x
  · exact rowEval10468 x

theorem entryEval19_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_7 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck19_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_7]

def rows19_8 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10469, row10470, row10471, row10472, row10473, row10474, row10475, row10476, row10477, row10478]

theorem entryCheck19_8 : entry19_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_8 k)) := by decide +kernel

theorem rowsSound19_8 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval10469 x
  · exact rowEval10470 x
  · exact rowEval10471 x
  · exact rowEval10472 x
  · exact rowEval10473 x
  · exact rowEval10474 x
  · exact rowEval10475 x
  · exact rowEval10476 x
  · exact rowEval10477 x
  · exact rowEval10478 x

theorem entryEval19_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_8 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck19_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_8]

def rows19_9 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10479, row10480, row10481, row10482, row10483, row10484, row10485, row10486, row10487, row10488]

theorem entryCheck19_9 : entry19_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_9 k)) := by decide +kernel

theorem rowsSound19_9 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval10479 x
  · exact rowEval10480 x
  · exact rowEval10481 x
  · exact rowEval10482 x
  · exact rowEval10483 x
  · exact rowEval10484 x
  · exact rowEval10485 x
  · exact rowEval10486 x
  · exact rowEval10487 x
  · exact rowEval10488 x

theorem entryEval19_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_9 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck19_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_9]

def rows19_10 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10489, row10490, row10491, row10492, row10493, row10494, row10495, row10496, row10497, row10498]

theorem entryCheck19_10 : entry19_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_10 k)) := by decide +kernel

theorem rowsSound19_10 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval10489 x
  · exact rowEval10490 x
  · exact rowEval10491 x
  · exact rowEval10492 x
  · exact rowEval10493 x
  · exact rowEval10494 x
  · exact rowEval10495 x
  · exact rowEval10496 x
  · exact rowEval10497 x
  · exact rowEval10498 x

theorem entryEval19_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_10 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck19_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_10]

def rows19_11 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10499, row10500, row10501, row10502, row10503, row10504, row10505, row10506, row10507, row10508]

theorem entryCheck19_11 : entry19_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_11 k)) := by decide +kernel

theorem rowsSound19_11 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval10499 x
  · exact rowEval10500 x
  · exact rowEval10501 x
  · exact rowEval10502 x
  · exact rowEval10503 x
  · exact rowEval10504 x
  · exact rowEval10505 x
  · exact rowEval10506 x
  · exact rowEval10507 x
  · exact rowEval10508 x

theorem entryEval19_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_11 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck19_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_11]

def rows19_12 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10509, row10510, row10511, row10512, row10513, row10514, row10515, row10516, row10517, row10518]

theorem entryCheck19_12 : entry19_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_12 k)) := by decide +kernel

theorem rowsSound19_12 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval10509 x
  · exact rowEval10510 x
  · exact rowEval10511 x
  · exact rowEval10512 x
  · exact rowEval10513 x
  · exact rowEval10514 x
  · exact rowEval10515 x
  · exact rowEval10516 x
  · exact rowEval10517 x
  · exact rowEval10518 x

theorem entryEval19_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_12 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck19_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_12]

def rows19_13 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10519, row10520, row10521, row10522, row10523, row10524, row10525, row10526, row10527, row10528]

theorem entryCheck19_13 : entry19_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_13 k)) := by decide +kernel

theorem rowsSound19_13 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval10519 x
  · exact rowEval10520 x
  · exact rowEval10521 x
  · exact rowEval10522 x
  · exact rowEval10523 x
  · exact rowEval10524 x
  · exact rowEval10525 x
  · exact rowEval10526 x
  · exact rowEval10527 x
  · exact rowEval10528 x

theorem entryEval19_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_13 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck19_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_13]

def rows19_14 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10529, row10530, row10531, row10532, row10533, row10534, row10535, row10536, row10537, row10538]

theorem entryCheck19_14 : entry19_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_14 k)) := by decide +kernel

theorem rowsSound19_14 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval10529 x
  · exact rowEval10530 x
  · exact rowEval10531 x
  · exact rowEval10532 x
  · exact rowEval10533 x
  · exact rowEval10534 x
  · exact rowEval10535 x
  · exact rowEval10536 x
  · exact rowEval10537 x
  · exact rowEval10538 x

theorem entryEval19_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_14 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck19_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_14]

def rows19_15 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10539, row10540, row10541, row10542, row10543, row10544, row10545, row10546, row10547, row10548]

theorem entryCheck19_15 : entry19_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_15 k)) := by decide +kernel

theorem rowsSound19_15 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval10539 x
  · exact rowEval10540 x
  · exact rowEval10541 x
  · exact rowEval10542 x
  · exact rowEval10543 x
  · exact rowEval10544 x
  · exact rowEval10545 x
  · exact rowEval10546 x
  · exact rowEval10547 x
  · exact rowEval10548 x

theorem entryEval19_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_15 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck19_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_15]

def rows19_16 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10549, row10550, row10551, row10552, row10553, row10554, row10555, row10556, row10557, row10558]

theorem entryCheck19_16 : entry19_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_16 k)) := by decide +kernel

theorem rowsSound19_16 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval10549 x
  · exact rowEval10550 x
  · exact rowEval10551 x
  · exact rowEval10552 x
  · exact rowEval10553 x
  · exact rowEval10554 x
  · exact rowEval10555 x
  · exact rowEval10556 x
  · exact rowEval10557 x
  · exact rowEval10558 x

theorem entryEval19_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_16 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck19_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_16]

def rows19_17 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10559, row10560, row10561, row10562, row10563, row10564, row10565, row10566, row10567, row10568]

theorem entryCheck19_17 : entry19_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_17 k)) := by decide +kernel

theorem rowsSound19_17 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval10559 x
  · exact rowEval10560 x
  · exact rowEval10561 x
  · exact rowEval10562 x
  · exact rowEval10563 x
  · exact rowEval10564 x
  · exact rowEval10565 x
  · exact rowEval10566 x
  · exact rowEval10567 x
  · exact rowEval10568 x

theorem entryEval19_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_17 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck19_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_17]

def rows19_18 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10569, row10570, row10571, row10572, row10573, row10574, row10575, row10576, row10577, row10578]

theorem entryCheck19_18 : entry19_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_18 k)) := by decide +kernel

theorem rowsSound19_18 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval10569 x
  · exact rowEval10570 x
  · exact rowEval10571 x
  · exact rowEval10572 x
  · exact rowEval10573 x
  · exact rowEval10574 x
  · exact rowEval10575 x
  · exact rowEval10576 x
  · exact rowEval10577 x
  · exact rowEval10578 x

theorem entryEval19_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_18 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck19_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_18]

def rows19_19 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10579, row10580, row10581, row10582, row10583, row10584, row10585, row10586, row10587, row10588]

theorem entryCheck19_19 : entry19_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_19 k)) := by decide +kernel

theorem rowsSound19_19 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval10579 x
  · exact rowEval10580 x
  · exact rowEval10581 x
  · exact rowEval10582 x
  · exact rowEval10583 x
  · exact rowEval10584 x
  · exact rowEval10585 x
  · exact rowEval10586 x
  · exact rowEval10587 x
  · exact rowEval10588 x

theorem entryEval19_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_19 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck19_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_19]

end MUB6.Certificate.GramEntries.Block3

end OAI
