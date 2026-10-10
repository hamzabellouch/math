import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block175
import OAI.Analysis.MutuallyUnbiased.GramRows.Block176
import OAI.Analysis.MutuallyUnbiased.GramRows.Block177

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19384, row19385, row19386, row19387, row19388, row19389, row19390, row19391, row19392, row19393, row19394, row19395, row19396, row19397, row19398, row19399, row19400, row19401, row19402, row19403]

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19384 x
  · exact rowEval19385 x
  · exact rowEval19386 x
  · exact rowEval19387 x
  · exact rowEval19388 x
  · exact rowEval19389 x
  · exact rowEval19390 x
  · exact rowEval19391 x
  · exact rowEval19392 x
  · exact rowEval19393 x
  · exact rowEval19394 x
  · exact rowEval19395 x
  · exact rowEval19396 x
  · exact rowEval19397 x
  · exact rowEval19398 x
  · exact rowEval19399 x
  · exact rowEval19400 x
  · exact rowEval19401 x
  · exact rowEval19402 x
  · exact rowEval19403 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

def rows10_1 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19404, row19405, row19406, row19407, row19408, row19409, row19410, row19411, row19412, row19413, row19414, row19415, row19416, row19417, row19418, row19419, row19420, row19421, row19422, row19423]

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19404 x
  · exact rowEval19405 x
  · exact rowEval19406 x
  · exact rowEval19407 x
  · exact rowEval19408 x
  · exact rowEval19409 x
  · exact rowEval19410 x
  · exact rowEval19411 x
  · exact rowEval19412 x
  · exact rowEval19413 x
  · exact rowEval19414 x
  · exact rowEval19415 x
  · exact rowEval19416 x
  · exact rowEval19417 x
  · exact rowEval19418 x
  · exact rowEval19419 x
  · exact rowEval19420 x
  · exact rowEval19421 x
  · exact rowEval19422 x
  · exact rowEval19423 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

def rows10_2 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19424, row19425, row19426, row19427, row19428, row19429, row19430, row19431, row19432, row19433, row19434, row19435, row19436, row19437, row19438, row19439, row19440, row19441, row19442, row19443]

theorem entryCheck10_2 : entry10_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_2 k)) := by decide +kernel

theorem rowsSound10_2 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval19424 x
  · exact rowEval19425 x
  · exact rowEval19426 x
  · exact rowEval19427 x
  · exact rowEval19428 x
  · exact rowEval19429 x
  · exact rowEval19430 x
  · exact rowEval19431 x
  · exact rowEval19432 x
  · exact rowEval19433 x
  · exact rowEval19434 x
  · exact rowEval19435 x
  · exact rowEval19436 x
  · exact rowEval19437 x
  · exact rowEval19438 x
  · exact rowEval19439 x
  · exact rowEval19440 x
  · exact rowEval19441 x
  · exact rowEval19442 x
  · exact rowEval19443 x

theorem entryEval10_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_2 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck10_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_2]

def rows10_3 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19444, row19445, row19446, row19447, row19448, row19449, row19450, row19451, row19452, row19453, row19454, row19455, row19456, row19457, row19458, row19459, row19460, row19461, row19462, row19463]

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19444 x
  · exact rowEval19445 x
  · exact rowEval19446 x
  · exact rowEval19447 x
  · exact rowEval19448 x
  · exact rowEval19449 x
  · exact rowEval19450 x
  · exact rowEval19451 x
  · exact rowEval19452 x
  · exact rowEval19453 x
  · exact rowEval19454 x
  · exact rowEval19455 x
  · exact rowEval19456 x
  · exact rowEval19457 x
  · exact rowEval19458 x
  · exact rowEval19459 x
  · exact rowEval19460 x
  · exact rowEval19461 x
  · exact rowEval19462 x
  · exact rowEval19463 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

def rows10_4 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19464, row19465, row19466, row19467, row19468, row19469, row19470, row19471, row19472, row19473, row19474, row19475, row19476, row19477, row19478, row19479, row19480, row19481, row19482, row19483]

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19464 x
  · exact rowEval19465 x
  · exact rowEval19466 x
  · exact rowEval19467 x
  · exact rowEval19468 x
  · exact rowEval19469 x
  · exact rowEval19470 x
  · exact rowEval19471 x
  · exact rowEval19472 x
  · exact rowEval19473 x
  · exact rowEval19474 x
  · exact rowEval19475 x
  · exact rowEval19476 x
  · exact rowEval19477 x
  · exact rowEval19478 x
  · exact rowEval19479 x
  · exact rowEval19480 x
  · exact rowEval19481 x
  · exact rowEval19482 x
  · exact rowEval19483 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

def rows10_5 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19484, row19485, row19486, row19487, row19488, row19489, row19490, row19491, row19492, row19493, row19494, row19495, row19496, row19497, row19498, row19499, row19500, row19501, row19502, row19503]

theorem entryCheck10_5 : entry10_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_5 k)) := by decide +kernel

theorem rowsSound10_5 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19484 x
  · exact rowEval19485 x
  · exact rowEval19486 x
  · exact rowEval19487 x
  · exact rowEval19488 x
  · exact rowEval19489 x
  · exact rowEval19490 x
  · exact rowEval19491 x
  · exact rowEval19492 x
  · exact rowEval19493 x
  · exact rowEval19494 x
  · exact rowEval19495 x
  · exact rowEval19496 x
  · exact rowEval19497 x
  · exact rowEval19498 x
  · exact rowEval19499 x
  · exact rowEval19500 x
  · exact rowEval19501 x
  · exact rowEval19502 x
  · exact rowEval19503 x

theorem entryEval10_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_5 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck10_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_5]

def rows10_6 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19504, row19505, row19506, row19507, row19508, row19509, row19510, row19511, row19512, row19513, row19514, row19515, row19516, row19517, row19518, row19519, row19520, row19521, row19522, row19523]

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19504 x
  · exact rowEval19505 x
  · exact rowEval19506 x
  · exact rowEval19507 x
  · exact rowEval19508 x
  · exact rowEval19509 x
  · exact rowEval19510 x
  · exact rowEval19511 x
  · exact rowEval19512 x
  · exact rowEval19513 x
  · exact rowEval19514 x
  · exact rowEval19515 x
  · exact rowEval19516 x
  · exact rowEval19517 x
  · exact rowEval19518 x
  · exact rowEval19519 x
  · exact rowEval19520 x
  · exact rowEval19521 x
  · exact rowEval19522 x
  · exact rowEval19523 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

def rows10_7 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19524, row19525, row19526, row19527, row19528, row19529, row19530, row19531, row19532, row19533, row19534, row19535, row19536, row19537, row19538, row19539, row19540, row19541, row19542, row19543]

theorem entryCheck10_7 : entry10_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_7 k)) := by decide +kernel

theorem rowsSound10_7 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval19524 x
  · exact rowEval19525 x
  · exact rowEval19526 x
  · exact rowEval19527 x
  · exact rowEval19528 x
  · exact rowEval19529 x
  · exact rowEval19530 x
  · exact rowEval19531 x
  · exact rowEval19532 x
  · exact rowEval19533 x
  · exact rowEval19534 x
  · exact rowEval19535 x
  · exact rowEval19536 x
  · exact rowEval19537 x
  · exact rowEval19538 x
  · exact rowEval19539 x
  · exact rowEval19540 x
  · exact rowEval19541 x
  · exact rowEval19542 x
  · exact rowEval19543 x

theorem entryEval10_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_7 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck10_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_7]

def rows10_8 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19544, row19545, row19546, row19547, row19548, row19549, row19550, row19551, row19552, row19553, row19554, row19555, row19556, row19557, row19558, row19559, row19560, row19561, row19562, row19563]

theorem entryCheck10_8 : entry10_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_8 k)) := by decide +kernel

theorem rowsSound10_8 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval19544 x
  · exact rowEval19545 x
  · exact rowEval19546 x
  · exact rowEval19547 x
  · exact rowEval19548 x
  · exact rowEval19549 x
  · exact rowEval19550 x
  · exact rowEval19551 x
  · exact rowEval19552 x
  · exact rowEval19553 x
  · exact rowEval19554 x
  · exact rowEval19555 x
  · exact rowEval19556 x
  · exact rowEval19557 x
  · exact rowEval19558 x
  · exact rowEval19559 x
  · exact rowEval19560 x
  · exact rowEval19561 x
  · exact rowEval19562 x
  · exact rowEval19563 x

theorem entryEval10_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_8 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck10_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_8]

def rows10_9 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19564, row19565, row19566, row19567, row19568, row19569, row19570, row19571, row19572, row19573, row19574, row19575, row19576, row19577, row19578, row19579, row19580, row19581, row19582, row19583]

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form9) x := by
  fin_cases k
  · exact rowEval19564 x
  · exact rowEval19565 x
  · exact rowEval19566 x
  · exact rowEval19567 x
  · exact rowEval19568 x
  · exact rowEval19569 x
  · exact rowEval19570 x
  · exact rowEval19571 x
  · exact rowEval19572 x
  · exact rowEval19573 x
  · exact rowEval19574 x
  · exact rowEval19575 x
  · exact rowEval19576 x
  · exact rowEval19577 x
  · exact rowEval19578 x
  · exact rowEval19579 x
  · exact rowEval19580 x
  · exact rowEval19581 x
  · exact rowEval19582 x
  · exact rowEval19583 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

def rows10_10 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19584, row19585, row19586, row19587, row19588, row19589, row19590, row19591, row19592, row19593, row19594, row19595, row19596, row19597, row19598, row19599, row19600, row19601, row19602, row19603]

theorem entryCheck10_10 : entry10_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_10 k)) := by decide +kernel

theorem rowsSound10_10 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form10) x := by
  fin_cases k
  · exact rowEval19584 x
  · exact rowEval19585 x
  · exact rowEval19586 x
  · exact rowEval19587 x
  · exact rowEval19588 x
  · exact rowEval19589 x
  · exact rowEval19590 x
  · exact rowEval19591 x
  · exact rowEval19592 x
  · exact rowEval19593 x
  · exact rowEval19594 x
  · exact rowEval19595 x
  · exact rowEval19596 x
  · exact rowEval19597 x
  · exact rowEval19598 x
  · exact rowEval19599 x
  · exact rowEval19600 x
  · exact rowEval19601 x
  · exact rowEval19602 x
  · exact rowEval19603 x

theorem entryEval10_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_10 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form10 B := by
  rw [entryCheck10_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_10]

end MUB6.Certificate.GramEntries.Block5

end OAI
