import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block129
import OAI.Analysis.MutuallyUnbiased.GramRows.Block130

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13485, row13486, row13487, row13488, row13489, row13490, row13491, row13492, row13493, row13494, row13495, row13496, row13497, row13498, row13499, row13500, row13501, row13502]

theorem entryCheck5_0 : entry5_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_0 k)) := by decide +kernel

theorem rowsSound5_0 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13485 x
  · exact rowEval13486 x
  · exact rowEval13487 x
  · exact rowEval13488 x
  · exact rowEval13489 x
  · exact rowEval13490 x
  · exact rowEval13491 x
  · exact rowEval13492 x
  · exact rowEval13493 x
  · exact rowEval13494 x
  · exact rowEval13495 x
  · exact rowEval13496 x
  · exact rowEval13497 x
  · exact rowEval13498 x
  · exact rowEval13499 x
  · exact rowEval13500 x
  · exact rowEval13501 x
  · exact rowEval13502 x

theorem entryEval5_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_0 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck5_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_0]

def rows5_1 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13503, row13504, row13505, row13506, row13507, row13508, row13509, row13510, row13511, row13512, row13513, row13514, row13515, row13516, row13517, row13518, row13519, row13520]

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13503 x
  · exact rowEval13504 x
  · exact rowEval13505 x
  · exact rowEval13506 x
  · exact rowEval13507 x
  · exact rowEval13508 x
  · exact rowEval13509 x
  · exact rowEval13510 x
  · exact rowEval13511 x
  · exact rowEval13512 x
  · exact rowEval13513 x
  · exact rowEval13514 x
  · exact rowEval13515 x
  · exact rowEval13516 x
  · exact rowEval13517 x
  · exact rowEval13518 x
  · exact rowEval13519 x
  · exact rowEval13520 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

def rows5_2 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13521, row13522, row13523, row13524, row13525, row13526, row13527, row13528, row13529, row13530, row13531, row13532, row13533, row13534, row13535, row13536, row13537, row13538]

theorem entryCheck5_2 : entry5_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_2 k)) := by decide +kernel

theorem rowsSound5_2 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13521 x
  · exact rowEval13522 x
  · exact rowEval13523 x
  · exact rowEval13524 x
  · exact rowEval13525 x
  · exact rowEval13526 x
  · exact rowEval13527 x
  · exact rowEval13528 x
  · exact rowEval13529 x
  · exact rowEval13530 x
  · exact rowEval13531 x
  · exact rowEval13532 x
  · exact rowEval13533 x
  · exact rowEval13534 x
  · exact rowEval13535 x
  · exact rowEval13536 x
  · exact rowEval13537 x
  · exact rowEval13538 x

theorem entryEval5_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_2 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck5_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_2]

def rows5_3 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13539, row13540, row13541, row13542, row13543, row13544, row13545, row13546, row13547, row13548, row13549, row13550, row13551, row13552, row13553, row13554, row13555, row13556]

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13539 x
  · exact rowEval13540 x
  · exact rowEval13541 x
  · exact rowEval13542 x
  · exact rowEval13543 x
  · exact rowEval13544 x
  · exact rowEval13545 x
  · exact rowEval13546 x
  · exact rowEval13547 x
  · exact rowEval13548 x
  · exact rowEval13549 x
  · exact rowEval13550 x
  · exact rowEval13551 x
  · exact rowEval13552 x
  · exact rowEval13553 x
  · exact rowEval13554 x
  · exact rowEval13555 x
  · exact rowEval13556 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

def rows5_4 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13557, row13558, row13559, row13560, row13561, row13562, row13563, row13564, row13565, row13566, row13567, row13568, row13569, row13570, row13571, row13572, row13573, row13574]

theorem entryCheck5_4 : entry5_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_4 k)) := by decide +kernel

theorem rowsSound5_4 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval13557 x
  · exact rowEval13558 x
  · exact rowEval13559 x
  · exact rowEval13560 x
  · exact rowEval13561 x
  · exact rowEval13562 x
  · exact rowEval13563 x
  · exact rowEval13564 x
  · exact rowEval13565 x
  · exact rowEval13566 x
  · exact rowEval13567 x
  · exact rowEval13568 x
  · exact rowEval13569 x
  · exact rowEval13570 x
  · exact rowEval13571 x
  · exact rowEval13572 x
  · exact rowEval13573 x
  · exact rowEval13574 x

theorem entryEval5_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_4 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck5_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_4]

def rows5_5 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13575, row13576, row13577, row13578, row13579, row13580, row13581, row13582, row13583, row13584, row13585, row13586, row13587, row13588, row13589, row13590, row13591, row13592]

theorem entryCheck5_5 : entry5_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_5 k)) := by decide +kernel

theorem rowsSound5_5 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval13575 x
  · exact rowEval13576 x
  · exact rowEval13577 x
  · exact rowEval13578 x
  · exact rowEval13579 x
  · exact rowEval13580 x
  · exact rowEval13581 x
  · exact rowEval13582 x
  · exact rowEval13583 x
  · exact rowEval13584 x
  · exact rowEval13585 x
  · exact rowEval13586 x
  · exact rowEval13587 x
  · exact rowEval13588 x
  · exact rowEval13589 x
  · exact rowEval13590 x
  · exact rowEval13591 x
  · exact rowEval13592 x

theorem entryEval5_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_5 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck5_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
