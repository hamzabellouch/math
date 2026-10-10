import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block121
import OAI.Analysis.MutuallyUnbiased.GramRows.Block122
import OAI.Analysis.MutuallyUnbiased.GramRows.Block123
import OAI.Analysis.MutuallyUnbiased.GramRows.Block124
import OAI.Analysis.MutuallyUnbiased.GramRows.Block125
import OAI.Analysis.MutuallyUnbiased.GramRows.Block126
import OAI.Analysis.MutuallyUnbiased.GramRows.Block127

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows26_0 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12539, row12540, row12541, row12542, row12543, row12544, row12545, row12546, row12547, row12548, row12549, row12550, row12551, row12552, row12553, row12554, row12555, row12556, row12557, row12558, row12559, row12560, row12561, row12562]

theorem entryCheck26_0 : entry26_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_0 k)) := by decide +kernel

theorem rowsSound26_0 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval12539 x
  · exact rowEval12540 x
  · exact rowEval12541 x
  · exact rowEval12542 x
  · exact rowEval12543 x
  · exact rowEval12544 x
  · exact rowEval12545 x
  · exact rowEval12546 x
  · exact rowEval12547 x
  · exact rowEval12548 x
  · exact rowEval12549 x
  · exact rowEval12550 x
  · exact rowEval12551 x
  · exact rowEval12552 x
  · exact rowEval12553 x
  · exact rowEval12554 x
  · exact rowEval12555 x
  · exact rowEval12556 x
  · exact rowEval12557 x
  · exact rowEval12558 x
  · exact rowEval12559 x
  · exact rowEval12560 x
  · exact rowEval12561 x
  · exact rowEval12562 x

theorem entryEval26_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_0 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck26_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_0]

def rows26_1 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12563, row12564, row12565, row12566, row12567, row12568, row12569, row12570, row12571, row12572, row12573, row12574, row12575, row12576, row12577, row12578, row12579, row12580, row12581, row12582, row12583, row12584, row12585, row12586]

theorem entryCheck26_1 : entry26_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_1 k)) := by decide +kernel

theorem rowsSound26_1 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval12563 x
  · exact rowEval12564 x
  · exact rowEval12565 x
  · exact rowEval12566 x
  · exact rowEval12567 x
  · exact rowEval12568 x
  · exact rowEval12569 x
  · exact rowEval12570 x
  · exact rowEval12571 x
  · exact rowEval12572 x
  · exact rowEval12573 x
  · exact rowEval12574 x
  · exact rowEval12575 x
  · exact rowEval12576 x
  · exact rowEval12577 x
  · exact rowEval12578 x
  · exact rowEval12579 x
  · exact rowEval12580 x
  · exact rowEval12581 x
  · exact rowEval12582 x
  · exact rowEval12583 x
  · exact rowEval12584 x
  · exact rowEval12585 x
  · exact rowEval12586 x

theorem entryEval26_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_1 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck26_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_1]

def rows26_2 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12587, row12588, row12589, row12590, row12591, row12592, row12593, row12594, row12595, row12596, row12597, row12598, row12599, row12600, row12601, row12602, row12603, row12604, row12605, row12606, row12607, row12608, row12609, row12610]

theorem entryCheck26_2 : entry26_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_2 k)) := by decide +kernel

theorem rowsSound26_2 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval12587 x
  · exact rowEval12588 x
  · exact rowEval12589 x
  · exact rowEval12590 x
  · exact rowEval12591 x
  · exact rowEval12592 x
  · exact rowEval12593 x
  · exact rowEval12594 x
  · exact rowEval12595 x
  · exact rowEval12596 x
  · exact rowEval12597 x
  · exact rowEval12598 x
  · exact rowEval12599 x
  · exact rowEval12600 x
  · exact rowEval12601 x
  · exact rowEval12602 x
  · exact rowEval12603 x
  · exact rowEval12604 x
  · exact rowEval12605 x
  · exact rowEval12606 x
  · exact rowEval12607 x
  · exact rowEval12608 x
  · exact rowEval12609 x
  · exact rowEval12610 x

theorem entryEval26_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_2 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck26_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_2]

def rows26_3 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12611, row12612, row12613, row12614, row12615, row12616, row12617, row12618, row12619, row12620, row12621, row12622, row12623, row12624, row12625, row12626, row12627, row12628, row12629, row12630, row12631, row12632, row12633, row12634]

theorem entryCheck26_3 : entry26_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_3 k)) := by decide +kernel

theorem rowsSound26_3 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval12611 x
  · exact rowEval12612 x
  · exact rowEval12613 x
  · exact rowEval12614 x
  · exact rowEval12615 x
  · exact rowEval12616 x
  · exact rowEval12617 x
  · exact rowEval12618 x
  · exact rowEval12619 x
  · exact rowEval12620 x
  · exact rowEval12621 x
  · exact rowEval12622 x
  · exact rowEval12623 x
  · exact rowEval12624 x
  · exact rowEval12625 x
  · exact rowEval12626 x
  · exact rowEval12627 x
  · exact rowEval12628 x
  · exact rowEval12629 x
  · exact rowEval12630 x
  · exact rowEval12631 x
  · exact rowEval12632 x
  · exact rowEval12633 x
  · exact rowEval12634 x

theorem entryEval26_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_3 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck26_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_3]

def rows26_4 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12635, row12636, row12637, row12638, row12639, row12640, row12641, row12642, row12643, row12644, row12645, row12646, row12647, row12648, row12649, row12650, row12651, row12652, row12653, row12654, row12655, row12656, row12657, row12658]

theorem entryCheck26_4 : entry26_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_4 k)) := by decide +kernel

theorem rowsSound26_4 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval12635 x
  · exact rowEval12636 x
  · exact rowEval12637 x
  · exact rowEval12638 x
  · exact rowEval12639 x
  · exact rowEval12640 x
  · exact rowEval12641 x
  · exact rowEval12642 x
  · exact rowEval12643 x
  · exact rowEval12644 x
  · exact rowEval12645 x
  · exact rowEval12646 x
  · exact rowEval12647 x
  · exact rowEval12648 x
  · exact rowEval12649 x
  · exact rowEval12650 x
  · exact rowEval12651 x
  · exact rowEval12652 x
  · exact rowEval12653 x
  · exact rowEval12654 x
  · exact rowEval12655 x
  · exact rowEval12656 x
  · exact rowEval12657 x
  · exact rowEval12658 x

theorem entryEval26_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_4 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck26_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_4]

def rows26_5 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12659, row12660, row12661, row12662, row12663, row12664, row12665, row12666, row12667, row12668, row12669, row12670, row12671, row12672, row12673, row12674, row12675, row12676, row12677, row12678, row12679, row12680, row12681, row12682]

theorem entryCheck26_5 : entry26_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_5 k)) := by decide +kernel

theorem rowsSound26_5 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval12659 x
  · exact rowEval12660 x
  · exact rowEval12661 x
  · exact rowEval12662 x
  · exact rowEval12663 x
  · exact rowEval12664 x
  · exact rowEval12665 x
  · exact rowEval12666 x
  · exact rowEval12667 x
  · exact rowEval12668 x
  · exact rowEval12669 x
  · exact rowEval12670 x
  · exact rowEval12671 x
  · exact rowEval12672 x
  · exact rowEval12673 x
  · exact rowEval12674 x
  · exact rowEval12675 x
  · exact rowEval12676 x
  · exact rowEval12677 x
  · exact rowEval12678 x
  · exact rowEval12679 x
  · exact rowEval12680 x
  · exact rowEval12681 x
  · exact rowEval12682 x

theorem entryEval26_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_5 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck26_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_5]

def rows26_6 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12683, row12684, row12685, row12686, row12687, row12688, row12689, row12690, row12691, row12692, row12693, row12694, row12695, row12696, row12697, row12698, row12699, row12700, row12701, row12702, row12703, row12704, row12705, row12706]

theorem entryCheck26_6 : entry26_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_6 k)) := by decide +kernel

theorem rowsSound26_6 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval12683 x
  · exact rowEval12684 x
  · exact rowEval12685 x
  · exact rowEval12686 x
  · exact rowEval12687 x
  · exact rowEval12688 x
  · exact rowEval12689 x
  · exact rowEval12690 x
  · exact rowEval12691 x
  · exact rowEval12692 x
  · exact rowEval12693 x
  · exact rowEval12694 x
  · exact rowEval12695 x
  · exact rowEval12696 x
  · exact rowEval12697 x
  · exact rowEval12698 x
  · exact rowEval12699 x
  · exact rowEval12700 x
  · exact rowEval12701 x
  · exact rowEval12702 x
  · exact rowEval12703 x
  · exact rowEval12704 x
  · exact rowEval12705 x
  · exact rowEval12706 x

theorem entryEval26_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_6 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck26_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_6]

def rows26_7 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12707, row12708, row12709, row12710, row12711, row12712, row12713, row12714, row12715, row12716, row12717, row12718, row12719, row12720, row12721, row12722, row12723, row12724, row12725, row12726, row12727, row12728, row12729, row12730]

theorem entryCheck26_7 : entry26_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_7 k)) := by decide +kernel

theorem rowsSound26_7 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval12707 x
  · exact rowEval12708 x
  · exact rowEval12709 x
  · exact rowEval12710 x
  · exact rowEval12711 x
  · exact rowEval12712 x
  · exact rowEval12713 x
  · exact rowEval12714 x
  · exact rowEval12715 x
  · exact rowEval12716 x
  · exact rowEval12717 x
  · exact rowEval12718 x
  · exact rowEval12719 x
  · exact rowEval12720 x
  · exact rowEval12721 x
  · exact rowEval12722 x
  · exact rowEval12723 x
  · exact rowEval12724 x
  · exact rowEval12725 x
  · exact rowEval12726 x
  · exact rowEval12727 x
  · exact rowEval12728 x
  · exact rowEval12729 x
  · exact rowEval12730 x

theorem entryEval26_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_7 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck26_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_7]

def rows26_8 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12731, row12732, row12733, row12734, row12735, row12736, row12737, row12738, row12739, row12740, row12741, row12742, row12743, row12744, row12745, row12746, row12747, row12748, row12749, row12750, row12751, row12752, row12753, row12754]

theorem entryCheck26_8 : entry26_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_8 k)) := by decide +kernel

theorem rowsSound26_8 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval12731 x
  · exact rowEval12732 x
  · exact rowEval12733 x
  · exact rowEval12734 x
  · exact rowEval12735 x
  · exact rowEval12736 x
  · exact rowEval12737 x
  · exact rowEval12738 x
  · exact rowEval12739 x
  · exact rowEval12740 x
  · exact rowEval12741 x
  · exact rowEval12742 x
  · exact rowEval12743 x
  · exact rowEval12744 x
  · exact rowEval12745 x
  · exact rowEval12746 x
  · exact rowEval12747 x
  · exact rowEval12748 x
  · exact rowEval12749 x
  · exact rowEval12750 x
  · exact rowEval12751 x
  · exact rowEval12752 x
  · exact rowEval12753 x
  · exact rowEval12754 x

theorem entryEval26_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_8 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck26_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_8]

def rows26_9 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12755, row12756, row12757, row12758, row12759, row12760, row12761, row12762, row12763, row12764, row12765, row12766, row12767, row12768, row12769, row12770, row12771, row12772, row12773, row12774, row12775, row12776, row12777, row12778]

theorem entryCheck26_9 : entry26_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_9 k)) := by decide +kernel

theorem rowsSound26_9 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval12755 x
  · exact rowEval12756 x
  · exact rowEval12757 x
  · exact rowEval12758 x
  · exact rowEval12759 x
  · exact rowEval12760 x
  · exact rowEval12761 x
  · exact rowEval12762 x
  · exact rowEval12763 x
  · exact rowEval12764 x
  · exact rowEval12765 x
  · exact rowEval12766 x
  · exact rowEval12767 x
  · exact rowEval12768 x
  · exact rowEval12769 x
  · exact rowEval12770 x
  · exact rowEval12771 x
  · exact rowEval12772 x
  · exact rowEval12773 x
  · exact rowEval12774 x
  · exact rowEval12775 x
  · exact rowEval12776 x
  · exact rowEval12777 x
  · exact rowEval12778 x

theorem entryEval26_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_9 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck26_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_9]

def rows26_10 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12779, row12780, row12781, row12782, row12783, row12784, row12785, row12786, row12787, row12788, row12789, row12790, row12791, row12792, row12793, row12794, row12795, row12796, row12797, row12798, row12799, row12800, row12801, row12802]

theorem entryCheck26_10 : entry26_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_10 k)) := by decide +kernel

theorem rowsSound26_10 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval12779 x
  · exact rowEval12780 x
  · exact rowEval12781 x
  · exact rowEval12782 x
  · exact rowEval12783 x
  · exact rowEval12784 x
  · exact rowEval12785 x
  · exact rowEval12786 x
  · exact rowEval12787 x
  · exact rowEval12788 x
  · exact rowEval12789 x
  · exact rowEval12790 x
  · exact rowEval12791 x
  · exact rowEval12792 x
  · exact rowEval12793 x
  · exact rowEval12794 x
  · exact rowEval12795 x
  · exact rowEval12796 x
  · exact rowEval12797 x
  · exact rowEval12798 x
  · exact rowEval12799 x
  · exact rowEval12800 x
  · exact rowEval12801 x
  · exact rowEval12802 x

theorem entryEval26_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_10 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck26_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_10]

def rows26_11 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12803, row12804, row12805, row12806, row12807, row12808, row12809, row12810, row12811, row12812, row12813, row12814, row12815, row12816, row12817, row12818, row12819, row12820, row12821, row12822, row12823, row12824, row12825, row12826]

theorem entryCheck26_11 : entry26_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_11 k)) := by decide +kernel

theorem rowsSound26_11 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval12803 x
  · exact rowEval12804 x
  · exact rowEval12805 x
  · exact rowEval12806 x
  · exact rowEval12807 x
  · exact rowEval12808 x
  · exact rowEval12809 x
  · exact rowEval12810 x
  · exact rowEval12811 x
  · exact rowEval12812 x
  · exact rowEval12813 x
  · exact rowEval12814 x
  · exact rowEval12815 x
  · exact rowEval12816 x
  · exact rowEval12817 x
  · exact rowEval12818 x
  · exact rowEval12819 x
  · exact rowEval12820 x
  · exact rowEval12821 x
  · exact rowEval12822 x
  · exact rowEval12823 x
  · exact rowEval12824 x
  · exact rowEval12825 x
  · exact rowEval12826 x

theorem entryEval26_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_11 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck26_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_11]

def rows26_12 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12827, row12828, row12829, row12830, row12831, row12832, row12833, row12834, row12835, row12836, row12837, row12838, row12839, row12840, row12841, row12842, row12843, row12844, row12845, row12846, row12847, row12848, row12849, row12850]

theorem entryCheck26_12 : entry26_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_12 k)) := by decide +kernel

theorem rowsSound26_12 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval12827 x
  · exact rowEval12828 x
  · exact rowEval12829 x
  · exact rowEval12830 x
  · exact rowEval12831 x
  · exact rowEval12832 x
  · exact rowEval12833 x
  · exact rowEval12834 x
  · exact rowEval12835 x
  · exact rowEval12836 x
  · exact rowEval12837 x
  · exact rowEval12838 x
  · exact rowEval12839 x
  · exact rowEval12840 x
  · exact rowEval12841 x
  · exact rowEval12842 x
  · exact rowEval12843 x
  · exact rowEval12844 x
  · exact rowEval12845 x
  · exact rowEval12846 x
  · exact rowEval12847 x
  · exact rowEval12848 x
  · exact rowEval12849 x
  · exact rowEval12850 x

theorem entryEval26_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_12 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck26_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_12]

def rows26_13 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12851, row12852, row12853, row12854, row12855, row12856, row12857, row12858, row12859, row12860, row12861, row12862, row12863, row12864, row12865, row12866, row12867, row12868, row12869, row12870, row12871, row12872, row12873, row12874]

theorem entryCheck26_13 : entry26_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_13 k)) := by decide +kernel

theorem rowsSound26_13 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12851 x
  · exact rowEval12852 x
  · exact rowEval12853 x
  · exact rowEval12854 x
  · exact rowEval12855 x
  · exact rowEval12856 x
  · exact rowEval12857 x
  · exact rowEval12858 x
  · exact rowEval12859 x
  · exact rowEval12860 x
  · exact rowEval12861 x
  · exact rowEval12862 x
  · exact rowEval12863 x
  · exact rowEval12864 x
  · exact rowEval12865 x
  · exact rowEval12866 x
  · exact rowEval12867 x
  · exact rowEval12868 x
  · exact rowEval12869 x
  · exact rowEval12870 x
  · exact rowEval12871 x
  · exact rowEval12872 x
  · exact rowEval12873 x
  · exact rowEval12874 x

theorem entryEval26_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_13 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck26_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_13]

def rows26_14 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12875, row12876, row12877, row12878, row12879, row12880, row12881, row12882, row12883, row12884, row12885, row12886, row12887, row12888, row12889, row12890, row12891, row12892, row12893, row12894, row12895, row12896, row12897, row12898]

theorem entryCheck26_14 : entry26_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_14 k)) := by decide +kernel

theorem rowsSound26_14 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12875 x
  · exact rowEval12876 x
  · exact rowEval12877 x
  · exact rowEval12878 x
  · exact rowEval12879 x
  · exact rowEval12880 x
  · exact rowEval12881 x
  · exact rowEval12882 x
  · exact rowEval12883 x
  · exact rowEval12884 x
  · exact rowEval12885 x
  · exact rowEval12886 x
  · exact rowEval12887 x
  · exact rowEval12888 x
  · exact rowEval12889 x
  · exact rowEval12890 x
  · exact rowEval12891 x
  · exact rowEval12892 x
  · exact rowEval12893 x
  · exact rowEval12894 x
  · exact rowEval12895 x
  · exact rowEval12896 x
  · exact rowEval12897 x
  · exact rowEval12898 x

theorem entryEval26_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_14 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck26_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_14]

def rows26_15 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12899, row12900, row12901, row12902, row12903, row12904, row12905, row12906, row12907, row12908, row12909, row12910, row12911, row12912, row12913, row12914, row12915, row12916, row12917, row12918, row12919, row12920, row12921, row12922]

theorem entryCheck26_15 : entry26_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_15 k)) := by decide +kernel

theorem rowsSound26_15 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12899 x
  · exact rowEval12900 x
  · exact rowEval12901 x
  · exact rowEval12902 x
  · exact rowEval12903 x
  · exact rowEval12904 x
  · exact rowEval12905 x
  · exact rowEval12906 x
  · exact rowEval12907 x
  · exact rowEval12908 x
  · exact rowEval12909 x
  · exact rowEval12910 x
  · exact rowEval12911 x
  · exact rowEval12912 x
  · exact rowEval12913 x
  · exact rowEval12914 x
  · exact rowEval12915 x
  · exact rowEval12916 x
  · exact rowEval12917 x
  · exact rowEval12918 x
  · exact rowEval12919 x
  · exact rowEval12920 x
  · exact rowEval12921 x
  · exact rowEval12922 x

theorem entryEval26_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_15 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck26_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_15]

def rows26_16 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12923, row12924, row12925, row12926, row12927, row12928, row12929, row12930, row12931, row12932, row12933, row12934, row12935, row12936, row12937, row12938, row12939, row12940, row12941, row12942, row12943, row12944, row12945, row12946]

theorem entryCheck26_16 : entry26_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_16 k)) := by decide +kernel

theorem rowsSound26_16 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12923 x
  · exact rowEval12924 x
  · exact rowEval12925 x
  · exact rowEval12926 x
  · exact rowEval12927 x
  · exact rowEval12928 x
  · exact rowEval12929 x
  · exact rowEval12930 x
  · exact rowEval12931 x
  · exact rowEval12932 x
  · exact rowEval12933 x
  · exact rowEval12934 x
  · exact rowEval12935 x
  · exact rowEval12936 x
  · exact rowEval12937 x
  · exact rowEval12938 x
  · exact rowEval12939 x
  · exact rowEval12940 x
  · exact rowEval12941 x
  · exact rowEval12942 x
  · exact rowEval12943 x
  · exact rowEval12944 x
  · exact rowEval12945 x
  · exact rowEval12946 x

theorem entryEval26_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_16 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck26_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_16]

def rows26_17 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12947, row12948, row12949, row12950, row12951, row12952, row12953, row12954, row12955, row12956, row12957, row12958, row12959, row12960, row12961, row12962, row12963, row12964, row12965, row12966, row12967, row12968, row12969, row12970]

theorem entryCheck26_17 : entry26_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_17 k)) := by decide +kernel

theorem rowsSound26_17 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12947 x
  · exact rowEval12948 x
  · exact rowEval12949 x
  · exact rowEval12950 x
  · exact rowEval12951 x
  · exact rowEval12952 x
  · exact rowEval12953 x
  · exact rowEval12954 x
  · exact rowEval12955 x
  · exact rowEval12956 x
  · exact rowEval12957 x
  · exact rowEval12958 x
  · exact rowEval12959 x
  · exact rowEval12960 x
  · exact rowEval12961 x
  · exact rowEval12962 x
  · exact rowEval12963 x
  · exact rowEval12964 x
  · exact rowEval12965 x
  · exact rowEval12966 x
  · exact rowEval12967 x
  · exact rowEval12968 x
  · exact rowEval12969 x
  · exact rowEval12970 x

theorem entryEval26_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_17 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck26_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_17]

def rows26_18 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12971, row12972, row12973, row12974, row12975, row12976, row12977, row12978, row12979, row12980, row12981, row12982, row12983, row12984, row12985, row12986, row12987, row12988, row12989, row12990, row12991, row12992, row12993, row12994]

theorem entryCheck26_18 : entry26_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_18 k)) := by decide +kernel

theorem rowsSound26_18 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval12971 x
  · exact rowEval12972 x
  · exact rowEval12973 x
  · exact rowEval12974 x
  · exact rowEval12975 x
  · exact rowEval12976 x
  · exact rowEval12977 x
  · exact rowEval12978 x
  · exact rowEval12979 x
  · exact rowEval12980 x
  · exact rowEval12981 x
  · exact rowEval12982 x
  · exact rowEval12983 x
  · exact rowEval12984 x
  · exact rowEval12985 x
  · exact rowEval12986 x
  · exact rowEval12987 x
  · exact rowEval12988 x
  · exact rowEval12989 x
  · exact rowEval12990 x
  · exact rowEval12991 x
  · exact rowEval12992 x
  · exact rowEval12993 x
  · exact rowEval12994 x

theorem entryEval26_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_18 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck26_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_18]

def rows26_19 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12995, row12996, row12997, row12998, row12999, row13000, row13001, row13002, row13003, row13004, row13005, row13006, row13007, row13008, row13009, row13010, row13011, row13012, row13013, row13014, row13015, row13016, row13017, row13018]

theorem entryCheck26_19 : entry26_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_19 k)) := by decide +kernel

theorem rowsSound26_19 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12995 x
  · exact rowEval12996 x
  · exact rowEval12997 x
  · exact rowEval12998 x
  · exact rowEval12999 x
  · exact rowEval13000 x
  · exact rowEval13001 x
  · exact rowEval13002 x
  · exact rowEval13003 x
  · exact rowEval13004 x
  · exact rowEval13005 x
  · exact rowEval13006 x
  · exact rowEval13007 x
  · exact rowEval13008 x
  · exact rowEval13009 x
  · exact rowEval13010 x
  · exact rowEval13011 x
  · exact rowEval13012 x
  · exact rowEval13013 x
  · exact rowEval13014 x
  · exact rowEval13015 x
  · exact rowEval13016 x
  · exact rowEval13017 x
  · exact rowEval13018 x

theorem entryEval26_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_19 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck26_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_19]

def rows26_20 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13019, row13020, row13021, row13022, row13023, row13024, row13025, row13026, row13027, row13028, row13029, row13030, row13031, row13032, row13033, row13034, row13035, row13036, row13037, row13038, row13039, row13040, row13041, row13042]

theorem entryCheck26_20 : entry26_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_20 k)) := by decide +kernel

theorem rowsSound26_20 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval13019 x
  · exact rowEval13020 x
  · exact rowEval13021 x
  · exact rowEval13022 x
  · exact rowEval13023 x
  · exact rowEval13024 x
  · exact rowEval13025 x
  · exact rowEval13026 x
  · exact rowEval13027 x
  · exact rowEval13028 x
  · exact rowEval13029 x
  · exact rowEval13030 x
  · exact rowEval13031 x
  · exact rowEval13032 x
  · exact rowEval13033 x
  · exact rowEval13034 x
  · exact rowEval13035 x
  · exact rowEval13036 x
  · exact rowEval13037 x
  · exact rowEval13038 x
  · exact rowEval13039 x
  · exact rowEval13040 x
  · exact rowEval13041 x
  · exact rowEval13042 x

theorem entryEval26_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_20 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck26_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_20]

def rows26_21 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13043, row13044, row13045, row13046, row13047, row13048, row13049, row13050, row13051, row13052, row13053, row13054, row13055, row13056, row13057, row13058, row13059, row13060, row13061, row13062, row13063, row13064, row13065, row13066]

theorem entryCheck26_21 : entry26_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_21 k)) := by decide +kernel

theorem rowsSound26_21 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
  · exact rowEval13043 x
  · exact rowEval13044 x
  · exact rowEval13045 x
  · exact rowEval13046 x
  · exact rowEval13047 x
  · exact rowEval13048 x
  · exact rowEval13049 x
  · exact rowEval13050 x
  · exact rowEval13051 x
  · exact rowEval13052 x
  · exact rowEval13053 x
  · exact rowEval13054 x
  · exact rowEval13055 x
  · exact rowEval13056 x
  · exact rowEval13057 x
  · exact rowEval13058 x
  · exact rowEval13059 x
  · exact rowEval13060 x
  · exact rowEval13061 x
  · exact rowEval13062 x
  · exact rowEval13063 x
  · exact rowEval13064 x
  · exact rowEval13065 x
  · exact rowEval13066 x

theorem entryEval26_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_21 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck26_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_21]

def rows26_22 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13067, row13068, row13069, row13070, row13071, row13072, row13073, row13074, row13075, row13076, row13077, row13078, row13079, row13080, row13081, row13082, row13083, row13084, row13085, row13086, row13087, row13088, row13089, row13090]

theorem entryCheck26_22 : entry26_22 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_22 k)) := by decide +kernel

theorem rowsSound26_22 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_22 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form22) x := by
  fin_cases k
  · exact rowEval13067 x
  · exact rowEval13068 x
  · exact rowEval13069 x
  · exact rowEval13070 x
  · exact rowEval13071 x
  · exact rowEval13072 x
  · exact rowEval13073 x
  · exact rowEval13074 x
  · exact rowEval13075 x
  · exact rowEval13076 x
  · exact rowEval13077 x
  · exact rowEval13078 x
  · exact rowEval13079 x
  · exact rowEval13080 x
  · exact rowEval13081 x
  · exact rowEval13082 x
  · exact rowEval13083 x
  · exact rowEval13084 x
  · exact rowEval13085 x
  · exact rowEval13086 x
  · exact rowEval13087 x
  · exact rowEval13088 x
  · exact rowEval13089 x
  · exact rowEval13090 x

theorem entryEval26_22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_22 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form22 B := by
  rw [entryCheck26_22, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form22 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_22]

def rows26_23 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13091, row13092, row13093, row13094, row13095, row13096, row13097, row13098, row13099, row13100, row13101, row13102, row13103, row13104, row13105, row13106, row13107, row13108, row13109, row13110, row13111, row13112, row13113, row13114]

theorem entryCheck26_23 : entry26_23 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_23 k)) := by decide +kernel

theorem rowsSound26_23 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_23 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form23) x := by
  fin_cases k
  · exact rowEval13091 x
  · exact rowEval13092 x
  · exact rowEval13093 x
  · exact rowEval13094 x
  · exact rowEval13095 x
  · exact rowEval13096 x
  · exact rowEval13097 x
  · exact rowEval13098 x
  · exact rowEval13099 x
  · exact rowEval13100 x
  · exact rowEval13101 x
  · exact rowEval13102 x
  · exact rowEval13103 x
  · exact rowEval13104 x
  · exact rowEval13105 x
  · exact rowEval13106 x
  · exact rowEval13107 x
  · exact rowEval13108 x
  · exact rowEval13109 x
  · exact rowEval13110 x
  · exact rowEval13111 x
  · exact rowEval13112 x
  · exact rowEval13113 x
  · exact rowEval13114 x

theorem entryEval26_23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_23 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form23 B := by
  rw [entryCheck26_23, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form23 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_23]

def rows26_24 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13115, row13116, row13117, row13118, row13119, row13120, row13121, row13122, row13123, row13124, row13125, row13126, row13127, row13128, row13129, row13130, row13131, row13132, row13133, row13134, row13135, row13136, row13137, row13138]

theorem entryCheck26_24 : entry26_24 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_24 k)) := by decide +kernel

theorem rowsSound26_24 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_24 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form24) x := by
  fin_cases k
  · exact rowEval13115 x
  · exact rowEval13116 x
  · exact rowEval13117 x
  · exact rowEval13118 x
  · exact rowEval13119 x
  · exact rowEval13120 x
  · exact rowEval13121 x
  · exact rowEval13122 x
  · exact rowEval13123 x
  · exact rowEval13124 x
  · exact rowEval13125 x
  · exact rowEval13126 x
  · exact rowEval13127 x
  · exact rowEval13128 x
  · exact rowEval13129 x
  · exact rowEval13130 x
  · exact rowEval13131 x
  · exact rowEval13132 x
  · exact rowEval13133 x
  · exact rowEval13134 x
  · exact rowEval13135 x
  · exact rowEval13136 x
  · exact rowEval13137 x
  · exact rowEval13138 x

theorem entryEval26_24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_24 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form24 B := by
  rw [entryCheck26_24, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form24 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_24]

def rows26_25 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13139, row13140, row13141, row13142, row13143, row13144, row13145, row13146, row13147, row13148, row13149, row13150, row13151, row13152, row13153, row13154, row13155, row13156, row13157, row13158, row13159, row13160, row13161, row13162]

theorem entryCheck26_25 : entry26_25 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_25 k)) := by decide +kernel

theorem rowsSound26_25 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_25 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form25) x := by
  fin_cases k
  · exact rowEval13139 x
  · exact rowEval13140 x
  · exact rowEval13141 x
  · exact rowEval13142 x
  · exact rowEval13143 x
  · exact rowEval13144 x
  · exact rowEval13145 x
  · exact rowEval13146 x
  · exact rowEval13147 x
  · exact rowEval13148 x
  · exact rowEval13149 x
  · exact rowEval13150 x
  · exact rowEval13151 x
  · exact rowEval13152 x
  · exact rowEval13153 x
  · exact rowEval13154 x
  · exact rowEval13155 x
  · exact rowEval13156 x
  · exact rowEval13157 x
  · exact rowEval13158 x
  · exact rowEval13159 x
  · exact rowEval13160 x
  · exact rowEval13161 x
  · exact rowEval13162 x

theorem entryEval26_25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_25 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form25 B := by
  rw [entryCheck26_25, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form25 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_25]

def rows26_26 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13163, row13164, row13165, row13166, row13167, row13168, row13169, row13170, row13171, row13172, row13173, row13174, row13175, row13176, row13177, row13178, row13179, row13180, row13181, row13182, row13183, row13184, row13185, row13186]

theorem entryCheck26_26 : entry26_26 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_26 k)) := by decide +kernel

theorem rowsSound26_26 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_26 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form26) x := by
  fin_cases k
  · exact rowEval13163 x
  · exact rowEval13164 x
  · exact rowEval13165 x
  · exact rowEval13166 x
  · exact rowEval13167 x
  · exact rowEval13168 x
  · exact rowEval13169 x
  · exact rowEval13170 x
  · exact rowEval13171 x
  · exact rowEval13172 x
  · exact rowEval13173 x
  · exact rowEval13174 x
  · exact rowEval13175 x
  · exact rowEval13176 x
  · exact rowEval13177 x
  · exact rowEval13178 x
  · exact rowEval13179 x
  · exact rowEval13180 x
  · exact rowEval13181 x
  · exact rowEval13182 x
  · exact rowEval13183 x
  · exact rowEval13184 x
  · exact rowEval13185 x
  · exact rowEval13186 x

theorem entryEval26_26 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_26 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form26 B := by
  rw [entryCheck26_26, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form26 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_26]

end MUB6.Certificate.GramEntries.Block3

end OAI
