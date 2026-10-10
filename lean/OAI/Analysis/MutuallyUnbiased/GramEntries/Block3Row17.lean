import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block98
import OAI.Analysis.MutuallyUnbiased.GramRows.Block99
import OAI.Analysis.MutuallyUnbiased.GramRows.Block100
import OAI.Analysis.MutuallyUnbiased.GramRows.Block101

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_0 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9501, row9502, row9503, row9504, row9505, row9506, row9507, row9508, row9509, row9510, row9511, row9512, row9513, row9514, row9515, row9516, row9517, row9518, row9519, row9520, row9521, row9522, row9523, row9524]

theorem entryCheck17_0 : entry17_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_0 k)) := by decide +kernel

theorem rowsSound17_0 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval9501 x
  · exact rowEval9502 x
  · exact rowEval9503 x
  · exact rowEval9504 x
  · exact rowEval9505 x
  · exact rowEval9506 x
  · exact rowEval9507 x
  · exact rowEval9508 x
  · exact rowEval9509 x
  · exact rowEval9510 x
  · exact rowEval9511 x
  · exact rowEval9512 x
  · exact rowEval9513 x
  · exact rowEval9514 x
  · exact rowEval9515 x
  · exact rowEval9516 x
  · exact rowEval9517 x
  · exact rowEval9518 x
  · exact rowEval9519 x
  · exact rowEval9520 x
  · exact rowEval9521 x
  · exact rowEval9522 x
  · exact rowEval9523 x
  · exact rowEval9524 x

theorem entryEval17_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_0 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck17_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_0]

def rows17_1 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9525, row9526, row9527, row9528, row9529, row9530, row9531, row9532, row9533, row9534, row9535, row9536, row9537, row9538, row9539, row9540, row9541, row9542, row9543, row9544, row9545, row9546, row9547, row9548]

theorem entryCheck17_1 : entry17_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_1 k)) := by decide +kernel

theorem rowsSound17_1 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval9525 x
  · exact rowEval9526 x
  · exact rowEval9527 x
  · exact rowEval9528 x
  · exact rowEval9529 x
  · exact rowEval9530 x
  · exact rowEval9531 x
  · exact rowEval9532 x
  · exact rowEval9533 x
  · exact rowEval9534 x
  · exact rowEval9535 x
  · exact rowEval9536 x
  · exact rowEval9537 x
  · exact rowEval9538 x
  · exact rowEval9539 x
  · exact rowEval9540 x
  · exact rowEval9541 x
  · exact rowEval9542 x
  · exact rowEval9543 x
  · exact rowEval9544 x
  · exact rowEval9545 x
  · exact rowEval9546 x
  · exact rowEval9547 x
  · exact rowEval9548 x

theorem entryEval17_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_1 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck17_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_1]

def rows17_2 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9549, row9550, row9551, row9552, row9553, row9554, row9555, row9556, row9557, row9558, row9559, row9560, row9561, row9562, row9563, row9564, row9565, row9566, row9567, row9568, row9569, row9570, row9571, row9572]

theorem entryCheck17_2 : entry17_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_2 k)) := by decide +kernel

theorem rowsSound17_2 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval9549 x
  · exact rowEval9550 x
  · exact rowEval9551 x
  · exact rowEval9552 x
  · exact rowEval9553 x
  · exact rowEval9554 x
  · exact rowEval9555 x
  · exact rowEval9556 x
  · exact rowEval9557 x
  · exact rowEval9558 x
  · exact rowEval9559 x
  · exact rowEval9560 x
  · exact rowEval9561 x
  · exact rowEval9562 x
  · exact rowEval9563 x
  · exact rowEval9564 x
  · exact rowEval9565 x
  · exact rowEval9566 x
  · exact rowEval9567 x
  · exact rowEval9568 x
  · exact rowEval9569 x
  · exact rowEval9570 x
  · exact rowEval9571 x
  · exact rowEval9572 x

theorem entryEval17_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_2 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck17_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_2]

def rows17_3 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9573, row9574, row9575, row9576, row9577, row9578, row9579, row9580, row9581, row9582, row9583, row9584, row9585, row9586, row9587, row9588, row9589, row9590, row9591, row9592, row9593, row9594, row9595, row9596]

theorem entryCheck17_3 : entry17_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_3 k)) := by decide +kernel

theorem rowsSound17_3 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval9573 x
  · exact rowEval9574 x
  · exact rowEval9575 x
  · exact rowEval9576 x
  · exact rowEval9577 x
  · exact rowEval9578 x
  · exact rowEval9579 x
  · exact rowEval9580 x
  · exact rowEval9581 x
  · exact rowEval9582 x
  · exact rowEval9583 x
  · exact rowEval9584 x
  · exact rowEval9585 x
  · exact rowEval9586 x
  · exact rowEval9587 x
  · exact rowEval9588 x
  · exact rowEval9589 x
  · exact rowEval9590 x
  · exact rowEval9591 x
  · exact rowEval9592 x
  · exact rowEval9593 x
  · exact rowEval9594 x
  · exact rowEval9595 x
  · exact rowEval9596 x

theorem entryEval17_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_3 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck17_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_3]

def rows17_4 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9597, row9598, row9599, row9600, row9601, row9602, row9603, row9604, row9605, row9606, row9607, row9608, row9609, row9610, row9611, row9612, row9613, row9614, row9615, row9616, row9617, row9618, row9619, row9620]

theorem entryCheck17_4 : entry17_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_4 k)) := by decide +kernel

theorem rowsSound17_4 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval9597 x
  · exact rowEval9598 x
  · exact rowEval9599 x
  · exact rowEval9600 x
  · exact rowEval9601 x
  · exact rowEval9602 x
  · exact rowEval9603 x
  · exact rowEval9604 x
  · exact rowEval9605 x
  · exact rowEval9606 x
  · exact rowEval9607 x
  · exact rowEval9608 x
  · exact rowEval9609 x
  · exact rowEval9610 x
  · exact rowEval9611 x
  · exact rowEval9612 x
  · exact rowEval9613 x
  · exact rowEval9614 x
  · exact rowEval9615 x
  · exact rowEval9616 x
  · exact rowEval9617 x
  · exact rowEval9618 x
  · exact rowEval9619 x
  · exact rowEval9620 x

theorem entryEval17_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_4 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck17_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_4]

def rows17_5 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9621, row9622, row9623, row9624, row9625, row9626, row9627, row9628, row9629, row9630, row9631, row9632, row9633, row9634, row9635, row9636, row9637, row9638, row9639, row9640, row9641, row9642, row9643, row9644]

theorem entryCheck17_5 : entry17_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_5 k)) := by decide +kernel

theorem rowsSound17_5 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval9621 x
  · exact rowEval9622 x
  · exact rowEval9623 x
  · exact rowEval9624 x
  · exact rowEval9625 x
  · exact rowEval9626 x
  · exact rowEval9627 x
  · exact rowEval9628 x
  · exact rowEval9629 x
  · exact rowEval9630 x
  · exact rowEval9631 x
  · exact rowEval9632 x
  · exact rowEval9633 x
  · exact rowEval9634 x
  · exact rowEval9635 x
  · exact rowEval9636 x
  · exact rowEval9637 x
  · exact rowEval9638 x
  · exact rowEval9639 x
  · exact rowEval9640 x
  · exact rowEval9641 x
  · exact rowEval9642 x
  · exact rowEval9643 x
  · exact rowEval9644 x

theorem entryEval17_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_5 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck17_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_5]

def rows17_6 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9645, row9646, row9647, row9648, row9649, row9650, row9651, row9652, row9653, row9654, row9655, row9656, row9657, row9658, row9659, row9660, row9661, row9662, row9663, row9664, row9665, row9666, row9667, row9668]

theorem entryCheck17_6 : entry17_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_6 k)) := by decide +kernel

theorem rowsSound17_6 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval9645 x
  · exact rowEval9646 x
  · exact rowEval9647 x
  · exact rowEval9648 x
  · exact rowEval9649 x
  · exact rowEval9650 x
  · exact rowEval9651 x
  · exact rowEval9652 x
  · exact rowEval9653 x
  · exact rowEval9654 x
  · exact rowEval9655 x
  · exact rowEval9656 x
  · exact rowEval9657 x
  · exact rowEval9658 x
  · exact rowEval9659 x
  · exact rowEval9660 x
  · exact rowEval9661 x
  · exact rowEval9662 x
  · exact rowEval9663 x
  · exact rowEval9664 x
  · exact rowEval9665 x
  · exact rowEval9666 x
  · exact rowEval9667 x
  · exact rowEval9668 x

theorem entryEval17_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_6 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck17_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_6]

def rows17_7 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9669, row9670, row9671, row9672, row9673, row9674, row9675, row9676, row9677, row9678, row9679, row9680, row9681, row9682, row9683, row9684, row9685, row9686, row9687, row9688, row9689, row9690, row9691, row9692]

theorem entryCheck17_7 : entry17_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_7 k)) := by decide +kernel

theorem rowsSound17_7 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval9669 x
  · exact rowEval9670 x
  · exact rowEval9671 x
  · exact rowEval9672 x
  · exact rowEval9673 x
  · exact rowEval9674 x
  · exact rowEval9675 x
  · exact rowEval9676 x
  · exact rowEval9677 x
  · exact rowEval9678 x
  · exact rowEval9679 x
  · exact rowEval9680 x
  · exact rowEval9681 x
  · exact rowEval9682 x
  · exact rowEval9683 x
  · exact rowEval9684 x
  · exact rowEval9685 x
  · exact rowEval9686 x
  · exact rowEval9687 x
  · exact rowEval9688 x
  · exact rowEval9689 x
  · exact rowEval9690 x
  · exact rowEval9691 x
  · exact rowEval9692 x

theorem entryEval17_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_7 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck17_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_7]

def rows17_8 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9693, row9694, row9695, row9696, row9697, row9698, row9699, row9700, row9701, row9702, row9703, row9704, row9705, row9706, row9707, row9708, row9709, row9710, row9711, row9712, row9713, row9714, row9715, row9716]

theorem entryCheck17_8 : entry17_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_8 k)) := by decide +kernel

theorem rowsSound17_8 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval9693 x
  · exact rowEval9694 x
  · exact rowEval9695 x
  · exact rowEval9696 x
  · exact rowEval9697 x
  · exact rowEval9698 x
  · exact rowEval9699 x
  · exact rowEval9700 x
  · exact rowEval9701 x
  · exact rowEval9702 x
  · exact rowEval9703 x
  · exact rowEval9704 x
  · exact rowEval9705 x
  · exact rowEval9706 x
  · exact rowEval9707 x
  · exact rowEval9708 x
  · exact rowEval9709 x
  · exact rowEval9710 x
  · exact rowEval9711 x
  · exact rowEval9712 x
  · exact rowEval9713 x
  · exact rowEval9714 x
  · exact rowEval9715 x
  · exact rowEval9716 x

theorem entryEval17_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_8 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck17_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_8]

def rows17_9 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9717, row9718, row9719, row9720, row9721, row9722, row9723, row9724, row9725, row9726, row9727, row9728, row9729, row9730, row9731, row9732, row9733, row9734, row9735, row9736, row9737, row9738, row9739, row9740]

theorem entryCheck17_9 : entry17_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_9 k)) := by decide +kernel

theorem rowsSound17_9 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval9717 x
  · exact rowEval9718 x
  · exact rowEval9719 x
  · exact rowEval9720 x
  · exact rowEval9721 x
  · exact rowEval9722 x
  · exact rowEval9723 x
  · exact rowEval9724 x
  · exact rowEval9725 x
  · exact rowEval9726 x
  · exact rowEval9727 x
  · exact rowEval9728 x
  · exact rowEval9729 x
  · exact rowEval9730 x
  · exact rowEval9731 x
  · exact rowEval9732 x
  · exact rowEval9733 x
  · exact rowEval9734 x
  · exact rowEval9735 x
  · exact rowEval9736 x
  · exact rowEval9737 x
  · exact rowEval9738 x
  · exact rowEval9739 x
  · exact rowEval9740 x

theorem entryEval17_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_9 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck17_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_9]

def rows17_10 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9741, row9742, row9743, row9744, row9745, row9746, row9747, row9748, row9749, row9750, row9751, row9752, row9753, row9754, row9755, row9756, row9757, row9758, row9759, row9760, row9761, row9762, row9763, row9764]

theorem entryCheck17_10 : entry17_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_10 k)) := by decide +kernel

theorem rowsSound17_10 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval9741 x
  · exact rowEval9742 x
  · exact rowEval9743 x
  · exact rowEval9744 x
  · exact rowEval9745 x
  · exact rowEval9746 x
  · exact rowEval9747 x
  · exact rowEval9748 x
  · exact rowEval9749 x
  · exact rowEval9750 x
  · exact rowEval9751 x
  · exact rowEval9752 x
  · exact rowEval9753 x
  · exact rowEval9754 x
  · exact rowEval9755 x
  · exact rowEval9756 x
  · exact rowEval9757 x
  · exact rowEval9758 x
  · exact rowEval9759 x
  · exact rowEval9760 x
  · exact rowEval9761 x
  · exact rowEval9762 x
  · exact rowEval9763 x
  · exact rowEval9764 x

theorem entryEval17_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_10 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck17_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_10]

def rows17_11 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9765, row9766, row9767, row9768, row9769, row9770, row9771, row9772, row9773, row9774, row9775, row9776, row9777, row9778, row9779, row9780, row9781, row9782, row9783, row9784, row9785, row9786, row9787, row9788]

theorem entryCheck17_11 : entry17_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_11 k)) := by decide +kernel

theorem rowsSound17_11 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval9765 x
  · exact rowEval9766 x
  · exact rowEval9767 x
  · exact rowEval9768 x
  · exact rowEval9769 x
  · exact rowEval9770 x
  · exact rowEval9771 x
  · exact rowEval9772 x
  · exact rowEval9773 x
  · exact rowEval9774 x
  · exact rowEval9775 x
  · exact rowEval9776 x
  · exact rowEval9777 x
  · exact rowEval9778 x
  · exact rowEval9779 x
  · exact rowEval9780 x
  · exact rowEval9781 x
  · exact rowEval9782 x
  · exact rowEval9783 x
  · exact rowEval9784 x
  · exact rowEval9785 x
  · exact rowEval9786 x
  · exact rowEval9787 x
  · exact rowEval9788 x

theorem entryEval17_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_11 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck17_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_11]

def rows17_12 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9789, row9790, row9791, row9792, row9793, row9794, row9795, row9796, row9797, row9798, row9799, row9800, row9801, row9802, row9803, row9804, row9805, row9806, row9807, row9808, row9809, row9810, row9811, row9812]

theorem entryCheck17_12 : entry17_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_12 k)) := by decide +kernel

theorem rowsSound17_12 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9789 x
  · exact rowEval9790 x
  · exact rowEval9791 x
  · exact rowEval9792 x
  · exact rowEval9793 x
  · exact rowEval9794 x
  · exact rowEval9795 x
  · exact rowEval9796 x
  · exact rowEval9797 x
  · exact rowEval9798 x
  · exact rowEval9799 x
  · exact rowEval9800 x
  · exact rowEval9801 x
  · exact rowEval9802 x
  · exact rowEval9803 x
  · exact rowEval9804 x
  · exact rowEval9805 x
  · exact rowEval9806 x
  · exact rowEval9807 x
  · exact rowEval9808 x
  · exact rowEval9809 x
  · exact rowEval9810 x
  · exact rowEval9811 x
  · exact rowEval9812 x

theorem entryEval17_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_12 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck17_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_12]

def rows17_13 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9813, row9814, row9815, row9816, row9817, row9818, row9819, row9820, row9821, row9822, row9823, row9824, row9825, row9826, row9827, row9828, row9829, row9830, row9831, row9832, row9833, row9834, row9835, row9836]

theorem entryCheck17_13 : entry17_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_13 k)) := by decide +kernel

theorem rowsSound17_13 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9813 x
  · exact rowEval9814 x
  · exact rowEval9815 x
  · exact rowEval9816 x
  · exact rowEval9817 x
  · exact rowEval9818 x
  · exact rowEval9819 x
  · exact rowEval9820 x
  · exact rowEval9821 x
  · exact rowEval9822 x
  · exact rowEval9823 x
  · exact rowEval9824 x
  · exact rowEval9825 x
  · exact rowEval9826 x
  · exact rowEval9827 x
  · exact rowEval9828 x
  · exact rowEval9829 x
  · exact rowEval9830 x
  · exact rowEval9831 x
  · exact rowEval9832 x
  · exact rowEval9833 x
  · exact rowEval9834 x
  · exact rowEval9835 x
  · exact rowEval9836 x

theorem entryEval17_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_13 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck17_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_13]

def rows17_14 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9837, row9838, row9839, row9840, row9841, row9842, row9843, row9844, row9845, row9846, row9847, row9848, row9849, row9850, row9851, row9852, row9853, row9854, row9855, row9856, row9857, row9858, row9859, row9860]

theorem entryCheck17_14 : entry17_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_14 k)) := by decide +kernel

theorem rowsSound17_14 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9837 x
  · exact rowEval9838 x
  · exact rowEval9839 x
  · exact rowEval9840 x
  · exact rowEval9841 x
  · exact rowEval9842 x
  · exact rowEval9843 x
  · exact rowEval9844 x
  · exact rowEval9845 x
  · exact rowEval9846 x
  · exact rowEval9847 x
  · exact rowEval9848 x
  · exact rowEval9849 x
  · exact rowEval9850 x
  · exact rowEval9851 x
  · exact rowEval9852 x
  · exact rowEval9853 x
  · exact rowEval9854 x
  · exact rowEval9855 x
  · exact rowEval9856 x
  · exact rowEval9857 x
  · exact rowEval9858 x
  · exact rowEval9859 x
  · exact rowEval9860 x

theorem entryEval17_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_14 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck17_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_14]

def rows17_15 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9861, row9862, row9863, row9864, row9865, row9866, row9867, row9868, row9869, row9870, row9871, row9872, row9873, row9874, row9875, row9876, row9877, row9878, row9879, row9880, row9881, row9882, row9883, row9884]

theorem entryCheck17_15 : entry17_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_15 k)) := by decide +kernel

theorem rowsSound17_15 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval9861 x
  · exact rowEval9862 x
  · exact rowEval9863 x
  · exact rowEval9864 x
  · exact rowEval9865 x
  · exact rowEval9866 x
  · exact rowEval9867 x
  · exact rowEval9868 x
  · exact rowEval9869 x
  · exact rowEval9870 x
  · exact rowEval9871 x
  · exact rowEval9872 x
  · exact rowEval9873 x
  · exact rowEval9874 x
  · exact rowEval9875 x
  · exact rowEval9876 x
  · exact rowEval9877 x
  · exact rowEval9878 x
  · exact rowEval9879 x
  · exact rowEval9880 x
  · exact rowEval9881 x
  · exact rowEval9882 x
  · exact rowEval9883 x
  · exact rowEval9884 x

theorem entryEval17_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_15 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck17_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_15]

def rows17_16 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9885, row9886, row9887, row9888, row9889, row9890, row9891, row9892, row9893, row9894, row9895, row9896, row9897, row9898, row9899, row9900, row9901, row9902, row9903, row9904, row9905, row9906, row9907, row9908]

theorem entryCheck17_16 : entry17_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_16 k)) := by decide +kernel

theorem rowsSound17_16 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval9885 x
  · exact rowEval9886 x
  · exact rowEval9887 x
  · exact rowEval9888 x
  · exact rowEval9889 x
  · exact rowEval9890 x
  · exact rowEval9891 x
  · exact rowEval9892 x
  · exact rowEval9893 x
  · exact rowEval9894 x
  · exact rowEval9895 x
  · exact rowEval9896 x
  · exact rowEval9897 x
  · exact rowEval9898 x
  · exact rowEval9899 x
  · exact rowEval9900 x
  · exact rowEval9901 x
  · exact rowEval9902 x
  · exact rowEval9903 x
  · exact rowEval9904 x
  · exact rowEval9905 x
  · exact rowEval9906 x
  · exact rowEval9907 x
  · exact rowEval9908 x

theorem entryEval17_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_16 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck17_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_16]

def rows17_17 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9909, row9910, row9911, row9912, row9913, row9914, row9915, row9916, row9917, row9918, row9919, row9920, row9921, row9922, row9923, row9924, row9925, row9926, row9927, row9928, row9929, row9930, row9931, row9932]

theorem entryCheck17_17 : entry17_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_17 k)) := by decide +kernel

theorem rowsSound17_17 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval9909 x
  · exact rowEval9910 x
  · exact rowEval9911 x
  · exact rowEval9912 x
  · exact rowEval9913 x
  · exact rowEval9914 x
  · exact rowEval9915 x
  · exact rowEval9916 x
  · exact rowEval9917 x
  · exact rowEval9918 x
  · exact rowEval9919 x
  · exact rowEval9920 x
  · exact rowEval9921 x
  · exact rowEval9922 x
  · exact rowEval9923 x
  · exact rowEval9924 x
  · exact rowEval9925 x
  · exact rowEval9926 x
  · exact rowEval9927 x
  · exact rowEval9928 x
  · exact rowEval9929 x
  · exact rowEval9930 x
  · exact rowEval9931 x
  · exact rowEval9932 x

theorem entryEval17_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_17 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck17_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_17]

end MUB6.Certificate.GramEntries.Block3

end OAI
