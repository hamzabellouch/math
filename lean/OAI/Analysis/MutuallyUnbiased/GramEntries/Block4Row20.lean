import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block161
import OAI.Analysis.MutuallyUnbiased.GramRows.Block162
import OAI.Analysis.MutuallyUnbiased.GramRows.Block163
import OAI.Analysis.MutuallyUnbiased.GramRows.Block164

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows20_0 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17611, row17612, row17613, row17614, row17615, row17616, row17617, row17618, row17619, row17620, row17621, row17622, row17623, row17624, row17625, row17626, row17627, row17628]

theorem entryCheck20_0 : entry20_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_0 k)) := by decide +kernel

theorem rowsSound20_0 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17611 x
  · exact rowEval17612 x
  · exact rowEval17613 x
  · exact rowEval17614 x
  · exact rowEval17615 x
  · exact rowEval17616 x
  · exact rowEval17617 x
  · exact rowEval17618 x
  · exact rowEval17619 x
  · exact rowEval17620 x
  · exact rowEval17621 x
  · exact rowEval17622 x
  · exact rowEval17623 x
  · exact rowEval17624 x
  · exact rowEval17625 x
  · exact rowEval17626 x
  · exact rowEval17627 x
  · exact rowEval17628 x

theorem entryEval20_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_0 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck20_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_0]

def rows20_1 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17629, row17630, row17631, row17632, row17633, row17634, row17635, row17636, row17637, row17638, row17639, row17640, row17641, row17642, row17643, row17644, row17645, row17646]

theorem entryCheck20_1 : entry20_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_1 k)) := by decide +kernel

theorem rowsSound20_1 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval17629 x
  · exact rowEval17630 x
  · exact rowEval17631 x
  · exact rowEval17632 x
  · exact rowEval17633 x
  · exact rowEval17634 x
  · exact rowEval17635 x
  · exact rowEval17636 x
  · exact rowEval17637 x
  · exact rowEval17638 x
  · exact rowEval17639 x
  · exact rowEval17640 x
  · exact rowEval17641 x
  · exact rowEval17642 x
  · exact rowEval17643 x
  · exact rowEval17644 x
  · exact rowEval17645 x
  · exact rowEval17646 x

theorem entryEval20_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_1 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck20_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_1]

def rows20_2 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17647, row17648, row17649, row17650, row17651, row17652, row17653, row17654, row17655, row17656, row17657, row17658, row17659, row17660, row17661, row17662, row17663, row17664]

theorem entryCheck20_2 : entry20_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_2 k)) := by decide +kernel

theorem rowsSound20_2 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval17647 x
  · exact rowEval17648 x
  · exact rowEval17649 x
  · exact rowEval17650 x
  · exact rowEval17651 x
  · exact rowEval17652 x
  · exact rowEval17653 x
  · exact rowEval17654 x
  · exact rowEval17655 x
  · exact rowEval17656 x
  · exact rowEval17657 x
  · exact rowEval17658 x
  · exact rowEval17659 x
  · exact rowEval17660 x
  · exact rowEval17661 x
  · exact rowEval17662 x
  · exact rowEval17663 x
  · exact rowEval17664 x

theorem entryEval20_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_2 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck20_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_2]

def rows20_3 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17665, row17666, row17667, row17668, row17669, row17670, row17671, row17672, row17673, row17674, row17675, row17676, row17677, row17678, row17679, row17680, row17681, row17682]

theorem entryCheck20_3 : entry20_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_3 k)) := by decide +kernel

theorem rowsSound20_3 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval17665 x
  · exact rowEval17666 x
  · exact rowEval17667 x
  · exact rowEval17668 x
  · exact rowEval17669 x
  · exact rowEval17670 x
  · exact rowEval17671 x
  · exact rowEval17672 x
  · exact rowEval17673 x
  · exact rowEval17674 x
  · exact rowEval17675 x
  · exact rowEval17676 x
  · exact rowEval17677 x
  · exact rowEval17678 x
  · exact rowEval17679 x
  · exact rowEval17680 x
  · exact rowEval17681 x
  · exact rowEval17682 x

theorem entryEval20_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_3 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck20_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_3]

def rows20_4 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17683, row17684, row17685, row17686, row17687, row17688, row17689, row17690, row17691, row17692, row17693, row17694, row17695, row17696, row17697, row17698, row17699, row17700]

theorem entryCheck20_4 : entry20_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_4 k)) := by decide +kernel

theorem rowsSound20_4 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval17683 x
  · exact rowEval17684 x
  · exact rowEval17685 x
  · exact rowEval17686 x
  · exact rowEval17687 x
  · exact rowEval17688 x
  · exact rowEval17689 x
  · exact rowEval17690 x
  · exact rowEval17691 x
  · exact rowEval17692 x
  · exact rowEval17693 x
  · exact rowEval17694 x
  · exact rowEval17695 x
  · exact rowEval17696 x
  · exact rowEval17697 x
  · exact rowEval17698 x
  · exact rowEval17699 x
  · exact rowEval17700 x

theorem entryEval20_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_4 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck20_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_4]

def rows20_5 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17701, row17702, row17703, row17704, row17705, row17706, row17707, row17708, row17709, row17710, row17711, row17712, row17713, row17714, row17715, row17716, row17717, row17718]

theorem entryCheck20_5 : entry20_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_5 k)) := by decide +kernel

theorem rowsSound20_5 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval17701 x
  · exact rowEval17702 x
  · exact rowEval17703 x
  · exact rowEval17704 x
  · exact rowEval17705 x
  · exact rowEval17706 x
  · exact rowEval17707 x
  · exact rowEval17708 x
  · exact rowEval17709 x
  · exact rowEval17710 x
  · exact rowEval17711 x
  · exact rowEval17712 x
  · exact rowEval17713 x
  · exact rowEval17714 x
  · exact rowEval17715 x
  · exact rowEval17716 x
  · exact rowEval17717 x
  · exact rowEval17718 x

theorem entryEval20_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_5 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck20_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_5]

def rows20_6 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17719, row17720, row17721, row17722, row17723, row17724, row17725, row17726, row17727, row17728, row17729, row17730, row17731, row17732, row17733, row17734, row17735, row17736]

theorem entryCheck20_6 : entry20_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_6 k)) := by decide +kernel

theorem rowsSound20_6 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval17719 x
  · exact rowEval17720 x
  · exact rowEval17721 x
  · exact rowEval17722 x
  · exact rowEval17723 x
  · exact rowEval17724 x
  · exact rowEval17725 x
  · exact rowEval17726 x
  · exact rowEval17727 x
  · exact rowEval17728 x
  · exact rowEval17729 x
  · exact rowEval17730 x
  · exact rowEval17731 x
  · exact rowEval17732 x
  · exact rowEval17733 x
  · exact rowEval17734 x
  · exact rowEval17735 x
  · exact rowEval17736 x

theorem entryEval20_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_6 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck20_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_6]

def rows20_7 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17737, row17738, row17739, row17740, row17741, row17742, row17743, row17744, row17745, row17746, row17747, row17748, row17749, row17750, row17751, row17752, row17753, row17754]

theorem entryCheck20_7 : entry20_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_7 k)) := by decide +kernel

theorem rowsSound20_7 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval17737 x
  · exact rowEval17738 x
  · exact rowEval17739 x
  · exact rowEval17740 x
  · exact rowEval17741 x
  · exact rowEval17742 x
  · exact rowEval17743 x
  · exact rowEval17744 x
  · exact rowEval17745 x
  · exact rowEval17746 x
  · exact rowEval17747 x
  · exact rowEval17748 x
  · exact rowEval17749 x
  · exact rowEval17750 x
  · exact rowEval17751 x
  · exact rowEval17752 x
  · exact rowEval17753 x
  · exact rowEval17754 x

theorem entryEval20_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_7 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck20_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_7]

def rows20_8 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17755, row17756, row17757, row17758, row17759, row17760, row17761, row17762, row17763, row17764, row17765, row17766, row17767, row17768, row17769, row17770, row17771, row17772]

theorem entryCheck20_8 : entry20_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_8 k)) := by decide +kernel

theorem rowsSound20_8 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval17755 x
  · exact rowEval17756 x
  · exact rowEval17757 x
  · exact rowEval17758 x
  · exact rowEval17759 x
  · exact rowEval17760 x
  · exact rowEval17761 x
  · exact rowEval17762 x
  · exact rowEval17763 x
  · exact rowEval17764 x
  · exact rowEval17765 x
  · exact rowEval17766 x
  · exact rowEval17767 x
  · exact rowEval17768 x
  · exact rowEval17769 x
  · exact rowEval17770 x
  · exact rowEval17771 x
  · exact rowEval17772 x

theorem entryEval20_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_8 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck20_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_8]

def rows20_9 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17773, row17774, row17775, row17776, row17777, row17778, row17779, row17780, row17781, row17782, row17783, row17784, row17785, row17786, row17787, row17788, row17789, row17790]

theorem entryCheck20_9 : entry20_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_9 k)) := by decide +kernel

theorem rowsSound20_9 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval17773 x
  · exact rowEval17774 x
  · exact rowEval17775 x
  · exact rowEval17776 x
  · exact rowEval17777 x
  · exact rowEval17778 x
  · exact rowEval17779 x
  · exact rowEval17780 x
  · exact rowEval17781 x
  · exact rowEval17782 x
  · exact rowEval17783 x
  · exact rowEval17784 x
  · exact rowEval17785 x
  · exact rowEval17786 x
  · exact rowEval17787 x
  · exact rowEval17788 x
  · exact rowEval17789 x
  · exact rowEval17790 x

theorem entryEval20_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_9 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck20_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_9]

def rows20_10 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17791, row17792, row17793, row17794, row17795, row17796, row17797, row17798, row17799, row17800, row17801, row17802, row17803, row17804, row17805, row17806, row17807, row17808]

theorem entryCheck20_10 : entry20_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_10 k)) := by decide +kernel

theorem rowsSound20_10 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval17791 x
  · exact rowEval17792 x
  · exact rowEval17793 x
  · exact rowEval17794 x
  · exact rowEval17795 x
  · exact rowEval17796 x
  · exact rowEval17797 x
  · exact rowEval17798 x
  · exact rowEval17799 x
  · exact rowEval17800 x
  · exact rowEval17801 x
  · exact rowEval17802 x
  · exact rowEval17803 x
  · exact rowEval17804 x
  · exact rowEval17805 x
  · exact rowEval17806 x
  · exact rowEval17807 x
  · exact rowEval17808 x

theorem entryEval20_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_10 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck20_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_10]

def rows20_11 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17809, row17810, row17811, row17812, row17813, row17814, row17815, row17816, row17817, row17818, row17819, row17820, row17821, row17822, row17823, row17824, row17825, row17826]

theorem entryCheck20_11 : entry20_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_11 k)) := by decide +kernel

theorem rowsSound20_11 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval17809 x
  · exact rowEval17810 x
  · exact rowEval17811 x
  · exact rowEval17812 x
  · exact rowEval17813 x
  · exact rowEval17814 x
  · exact rowEval17815 x
  · exact rowEval17816 x
  · exact rowEval17817 x
  · exact rowEval17818 x
  · exact rowEval17819 x
  · exact rowEval17820 x
  · exact rowEval17821 x
  · exact rowEval17822 x
  · exact rowEval17823 x
  · exact rowEval17824 x
  · exact rowEval17825 x
  · exact rowEval17826 x

theorem entryEval20_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_11 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck20_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_11]

def rows20_12 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17827, row17828, row17829, row17830, row17831, row17832, row17833, row17834, row17835, row17836, row17837, row17838, row17839, row17840, row17841, row17842, row17843, row17844]

theorem entryCheck20_12 : entry20_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_12 k)) := by decide +kernel

theorem rowsSound20_12 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval17827 x
  · exact rowEval17828 x
  · exact rowEval17829 x
  · exact rowEval17830 x
  · exact rowEval17831 x
  · exact rowEval17832 x
  · exact rowEval17833 x
  · exact rowEval17834 x
  · exact rowEval17835 x
  · exact rowEval17836 x
  · exact rowEval17837 x
  · exact rowEval17838 x
  · exact rowEval17839 x
  · exact rowEval17840 x
  · exact rowEval17841 x
  · exact rowEval17842 x
  · exact rowEval17843 x
  · exact rowEval17844 x

theorem entryEval20_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_12 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck20_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_12]

def rows20_13 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17845, row17846, row17847, row17848, row17849, row17850, row17851, row17852, row17853, row17854, row17855, row17856, row17857, row17858, row17859, row17860, row17861, row17862]

theorem entryCheck20_13 : entry20_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_13 k)) := by decide +kernel

theorem rowsSound20_13 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval17845 x
  · exact rowEval17846 x
  · exact rowEval17847 x
  · exact rowEval17848 x
  · exact rowEval17849 x
  · exact rowEval17850 x
  · exact rowEval17851 x
  · exact rowEval17852 x
  · exact rowEval17853 x
  · exact rowEval17854 x
  · exact rowEval17855 x
  · exact rowEval17856 x
  · exact rowEval17857 x
  · exact rowEval17858 x
  · exact rowEval17859 x
  · exact rowEval17860 x
  · exact rowEval17861 x
  · exact rowEval17862 x

theorem entryEval20_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_13 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck20_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_13]

def rows20_14 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17863, row17864, row17865, row17866, row17867, row17868, row17869, row17870, row17871, row17872, row17873, row17874, row17875, row17876, row17877, row17878, row17879, row17880]

theorem entryCheck20_14 : entry20_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_14 k)) := by decide +kernel

theorem rowsSound20_14 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form14) x := by
  fin_cases k
  · exact rowEval17863 x
  · exact rowEval17864 x
  · exact rowEval17865 x
  · exact rowEval17866 x
  · exact rowEval17867 x
  · exact rowEval17868 x
  · exact rowEval17869 x
  · exact rowEval17870 x
  · exact rowEval17871 x
  · exact rowEval17872 x
  · exact rowEval17873 x
  · exact rowEval17874 x
  · exact rowEval17875 x
  · exact rowEval17876 x
  · exact rowEval17877 x
  · exact rowEval17878 x
  · exact rowEval17879 x
  · exact rowEval17880 x

theorem entryEval20_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_14 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form14 B := by
  rw [entryCheck20_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_14]

def rows20_15 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17881, row17882, row17883, row17884, row17885, row17886, row17887, row17888, row17889, row17890, row17891, row17892, row17893, row17894, row17895, row17896, row17897, row17898]

theorem entryCheck20_15 : entry20_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_15 k)) := by decide +kernel

theorem rowsSound20_15 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form15) x := by
  fin_cases k
  · exact rowEval17881 x
  · exact rowEval17882 x
  · exact rowEval17883 x
  · exact rowEval17884 x
  · exact rowEval17885 x
  · exact rowEval17886 x
  · exact rowEval17887 x
  · exact rowEval17888 x
  · exact rowEval17889 x
  · exact rowEval17890 x
  · exact rowEval17891 x
  · exact rowEval17892 x
  · exact rowEval17893 x
  · exact rowEval17894 x
  · exact rowEval17895 x
  · exact rowEval17896 x
  · exact rowEval17897 x
  · exact rowEval17898 x

theorem entryEval20_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_15 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form15 B := by
  rw [entryCheck20_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_15]

def rows20_16 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17899, row17900, row17901, row17902, row17903, row17904, row17905, row17906, row17907, row17908, row17909, row17910, row17911, row17912, row17913, row17914, row17915, row17916]

theorem entryCheck20_16 : entry20_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_16 k)) := by decide +kernel

theorem rowsSound20_16 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form16) x := by
  fin_cases k
  · exact rowEval17899 x
  · exact rowEval17900 x
  · exact rowEval17901 x
  · exact rowEval17902 x
  · exact rowEval17903 x
  · exact rowEval17904 x
  · exact rowEval17905 x
  · exact rowEval17906 x
  · exact rowEval17907 x
  · exact rowEval17908 x
  · exact rowEval17909 x
  · exact rowEval17910 x
  · exact rowEval17911 x
  · exact rowEval17912 x
  · exact rowEval17913 x
  · exact rowEval17914 x
  · exact rowEval17915 x
  · exact rowEval17916 x

theorem entryEval20_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_16 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form16 B := by
  rw [entryCheck20_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_16]

def rows20_17 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17917, row17918, row17919, row17920, row17921, row17922, row17923, row17924, row17925, row17926, row17927, row17928, row17929, row17930, row17931, row17932, row17933, row17934]

theorem entryCheck20_17 : entry20_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_17 k)) := by decide +kernel

theorem rowsSound20_17 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval17917 x
  · exact rowEval17918 x
  · exact rowEval17919 x
  · exact rowEval17920 x
  · exact rowEval17921 x
  · exact rowEval17922 x
  · exact rowEval17923 x
  · exact rowEval17924 x
  · exact rowEval17925 x
  · exact rowEval17926 x
  · exact rowEval17927 x
  · exact rowEval17928 x
  · exact rowEval17929 x
  · exact rowEval17930 x
  · exact rowEval17931 x
  · exact rowEval17932 x
  · exact rowEval17933 x
  · exact rowEval17934 x

theorem entryEval20_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_17 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck20_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_17]

def rows20_18 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17935, row17936, row17937, row17938, row17939, row17940, row17941, row17942, row17943, row17944, row17945, row17946, row17947, row17948, row17949, row17950, row17951, row17952]

theorem entryCheck20_18 : entry20_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_18 k)) := by decide +kernel

theorem rowsSound20_18 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form18) x := by
  fin_cases k
  · exact rowEval17935 x
  · exact rowEval17936 x
  · exact rowEval17937 x
  · exact rowEval17938 x
  · exact rowEval17939 x
  · exact rowEval17940 x
  · exact rowEval17941 x
  · exact rowEval17942 x
  · exact rowEval17943 x
  · exact rowEval17944 x
  · exact rowEval17945 x
  · exact rowEval17946 x
  · exact rowEval17947 x
  · exact rowEval17948 x
  · exact rowEval17949 x
  · exact rowEval17950 x
  · exact rowEval17951 x
  · exact rowEval17952 x

theorem entryEval20_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_18 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form18 B := by
  rw [entryCheck20_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_18]

def rows20_19 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17953, row17954, row17955, row17956, row17957, row17958, row17959, row17960, row17961, row17962, row17963, row17964, row17965, row17966, row17967, row17968, row17969, row17970]

theorem entryCheck20_19 : entry20_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_19 k)) := by decide +kernel

theorem rowsSound20_19 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form19) x := by
  fin_cases k
  · exact rowEval17953 x
  · exact rowEval17954 x
  · exact rowEval17955 x
  · exact rowEval17956 x
  · exact rowEval17957 x
  · exact rowEval17958 x
  · exact rowEval17959 x
  · exact rowEval17960 x
  · exact rowEval17961 x
  · exact rowEval17962 x
  · exact rowEval17963 x
  · exact rowEval17964 x
  · exact rowEval17965 x
  · exact rowEval17966 x
  · exact rowEval17967 x
  · exact rowEval17968 x
  · exact rowEval17969 x
  · exact rowEval17970 x

theorem entryEval20_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_19 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form19 B := by
  rw [entryCheck20_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_19]

def rows20_20 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17971, row17972, row17973, row17974, row17975, row17976, row17977, row17978, row17979, row17980, row17981, row17982, row17983, row17984, row17985, row17986, row17987, row17988]

theorem entryCheck20_20 : entry20_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_20 k)) := by decide +kernel

theorem rowsSound20_20 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form20) x := by
  fin_cases k
  · exact rowEval17971 x
  · exact rowEval17972 x
  · exact rowEval17973 x
  · exact rowEval17974 x
  · exact rowEval17975 x
  · exact rowEval17976 x
  · exact rowEval17977 x
  · exact rowEval17978 x
  · exact rowEval17979 x
  · exact rowEval17980 x
  · exact rowEval17981 x
  · exact rowEval17982 x
  · exact rowEval17983 x
  · exact rowEval17984 x
  · exact rowEval17985 x
  · exact rowEval17986 x
  · exact rowEval17987 x
  · exact rowEval17988 x

theorem entryEval20_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_20 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form20 B := by
  rw [entryCheck20_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_20]

end MUB6.Certificate.GramEntries.Block4

end OAI
