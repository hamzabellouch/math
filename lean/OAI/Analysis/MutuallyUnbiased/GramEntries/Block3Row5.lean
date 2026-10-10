import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block83
import OAI.Analysis.MutuallyUnbiased.GramRows.Block84

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7574, row7575, row7576, row7577, row7578, row7579, row7580, row7581, row7582, row7583, row7584, row7585, row7586, row7587, row7588, row7589, row7590, row7591, row7592, row7593, row7594, row7595, row7596, row7597, row7598, row7599, row7600, row7601, row7602, row7603, row7604, row7605, row7606, row7607, row7608, row7609]

theorem entryCheck5_0 : entry5_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_0 k)) := by decide +kernel

theorem rowsSound5_0 (k : Fin GramFunctions.Block3.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form5.terms k).tag (GramFunctions.Block3.form5.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7574 x
  · exact rowEval7575 x
  · exact rowEval7576 x
  · exact rowEval7577 x
  · exact rowEval7578 x
  · exact rowEval7579 x
  · exact rowEval7580 x
  · exact rowEval7581 x
  · exact rowEval7582 x
  · exact rowEval7583 x
  · exact rowEval7584 x
  · exact rowEval7585 x
  · exact rowEval7586 x
  · exact rowEval7587 x
  · exact rowEval7588 x
  · exact rowEval7589 x
  · exact rowEval7590 x
  · exact rowEval7591 x
  · exact rowEval7592 x
  · exact rowEval7593 x
  · exact rowEval7594 x
  · exact rowEval7595 x
  · exact rowEval7596 x
  · exact rowEval7597 x
  · exact rowEval7598 x
  · exact rowEval7599 x
  · exact rowEval7600 x
  · exact rowEval7601 x
  · exact rowEval7602 x
  · exact rowEval7603 x
  · exact rowEval7604 x
  · exact rowEval7605 x
  · exact rowEval7606 x
  · exact rowEval7607 x
  · exact rowEval7608 x
  · exact rowEval7609 x

theorem entryEval5_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_0 (GramNormalization.eval B) = GramFunctions.Block3.form5.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck5_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form5 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_0]

def rows5_1 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7610, row7611, row7612, row7613, row7614, row7615, row7616, row7617, row7618, row7619, row7620, row7621, row7622, row7623, row7624, row7625, row7626, row7627, row7628, row7629, row7630, row7631, row7632, row7633, row7634, row7635, row7636, row7637, row7638, row7639, row7640, row7641, row7642, row7643, row7644, row7645]

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block3.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form5.terms k).tag (GramFunctions.Block3.form5.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7610 x
  · exact rowEval7611 x
  · exact rowEval7612 x
  · exact rowEval7613 x
  · exact rowEval7614 x
  · exact rowEval7615 x
  · exact rowEval7616 x
  · exact rowEval7617 x
  · exact rowEval7618 x
  · exact rowEval7619 x
  · exact rowEval7620 x
  · exact rowEval7621 x
  · exact rowEval7622 x
  · exact rowEval7623 x
  · exact rowEval7624 x
  · exact rowEval7625 x
  · exact rowEval7626 x
  · exact rowEval7627 x
  · exact rowEval7628 x
  · exact rowEval7629 x
  · exact rowEval7630 x
  · exact rowEval7631 x
  · exact rowEval7632 x
  · exact rowEval7633 x
  · exact rowEval7634 x
  · exact rowEval7635 x
  · exact rowEval7636 x
  · exact rowEval7637 x
  · exact rowEval7638 x
  · exact rowEval7639 x
  · exact rowEval7640 x
  · exact rowEval7641 x
  · exact rowEval7642 x
  · exact rowEval7643 x
  · exact rowEval7644 x
  · exact rowEval7645 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block3.form5.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form5 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

def rows5_2 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7646, row7647, row7648, row7649, row7650, row7651, row7652, row7653, row7654, row7655, row7656, row7657, row7658, row7659, row7660, row7661, row7662, row7663, row7664, row7665, row7666, row7667, row7668, row7669, row7670, row7671, row7672, row7673, row7674, row7675, row7676, row7677, row7678, row7679, row7680, row7681]

theorem entryCheck5_2 : entry5_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_2 k)) := by decide +kernel

theorem rowsSound5_2 (k : Fin GramFunctions.Block3.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form5.terms k).tag (GramFunctions.Block3.form5.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7646 x
  · exact rowEval7647 x
  · exact rowEval7648 x
  · exact rowEval7649 x
  · exact rowEval7650 x
  · exact rowEval7651 x
  · exact rowEval7652 x
  · exact rowEval7653 x
  · exact rowEval7654 x
  · exact rowEval7655 x
  · exact rowEval7656 x
  · exact rowEval7657 x
  · exact rowEval7658 x
  · exact rowEval7659 x
  · exact rowEval7660 x
  · exact rowEval7661 x
  · exact rowEval7662 x
  · exact rowEval7663 x
  · exact rowEval7664 x
  · exact rowEval7665 x
  · exact rowEval7666 x
  · exact rowEval7667 x
  · exact rowEval7668 x
  · exact rowEval7669 x
  · exact rowEval7670 x
  · exact rowEval7671 x
  · exact rowEval7672 x
  · exact rowEval7673 x
  · exact rowEval7674 x
  · exact rowEval7675 x
  · exact rowEval7676 x
  · exact rowEval7677 x
  · exact rowEval7678 x
  · exact rowEval7679 x
  · exact rowEval7680 x
  · exact rowEval7681 x

theorem entryEval5_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_2 (GramNormalization.eval B) = GramFunctions.Block3.form5.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck5_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form5 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_2]

def rows5_3 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7682, row7683, row7684, row7685, row7686, row7687, row7688, row7689, row7690, row7691, row7692, row7693, row7694, row7695, row7696, row7697, row7698, row7699, row7700, row7701, row7702, row7703, row7704, row7705, row7706, row7707, row7708, row7709, row7710, row7711, row7712, row7713, row7714, row7715, row7716, row7717]

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block3.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form5.terms k).tag (GramFunctions.Block3.form5.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7682 x
  · exact rowEval7683 x
  · exact rowEval7684 x
  · exact rowEval7685 x
  · exact rowEval7686 x
  · exact rowEval7687 x
  · exact rowEval7688 x
  · exact rowEval7689 x
  · exact rowEval7690 x
  · exact rowEval7691 x
  · exact rowEval7692 x
  · exact rowEval7693 x
  · exact rowEval7694 x
  · exact rowEval7695 x
  · exact rowEval7696 x
  · exact rowEval7697 x
  · exact rowEval7698 x
  · exact rowEval7699 x
  · exact rowEval7700 x
  · exact rowEval7701 x
  · exact rowEval7702 x
  · exact rowEval7703 x
  · exact rowEval7704 x
  · exact rowEval7705 x
  · exact rowEval7706 x
  · exact rowEval7707 x
  · exact rowEval7708 x
  · exact rowEval7709 x
  · exact rowEval7710 x
  · exact rowEval7711 x
  · exact rowEval7712 x
  · exact rowEval7713 x
  · exact rowEval7714 x
  · exact rowEval7715 x
  · exact rowEval7716 x
  · exact rowEval7717 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block3.form5.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form5 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

def rows5_4 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7718, row7719, row7720, row7721, row7722, row7723, row7724, row7725, row7726, row7727, row7728, row7729, row7730, row7731, row7732, row7733, row7734, row7735, row7736, row7737, row7738, row7739, row7740, row7741, row7742, row7743, row7744, row7745, row7746, row7747, row7748, row7749, row7750, row7751, row7752, row7753]

theorem entryCheck5_4 : entry5_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_4 k)) := by decide +kernel

theorem rowsSound5_4 (k : Fin GramFunctions.Block3.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form5.terms k).tag (GramFunctions.Block3.form5.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7718 x
  · exact rowEval7719 x
  · exact rowEval7720 x
  · exact rowEval7721 x
  · exact rowEval7722 x
  · exact rowEval7723 x
  · exact rowEval7724 x
  · exact rowEval7725 x
  · exact rowEval7726 x
  · exact rowEval7727 x
  · exact rowEval7728 x
  · exact rowEval7729 x
  · exact rowEval7730 x
  · exact rowEval7731 x
  · exact rowEval7732 x
  · exact rowEval7733 x
  · exact rowEval7734 x
  · exact rowEval7735 x
  · exact rowEval7736 x
  · exact rowEval7737 x
  · exact rowEval7738 x
  · exact rowEval7739 x
  · exact rowEval7740 x
  · exact rowEval7741 x
  · exact rowEval7742 x
  · exact rowEval7743 x
  · exact rowEval7744 x
  · exact rowEval7745 x
  · exact rowEval7746 x
  · exact rowEval7747 x
  · exact rowEval7748 x
  · exact rowEval7749 x
  · exact rowEval7750 x
  · exact rowEval7751 x
  · exact rowEval7752 x
  · exact rowEval7753 x

theorem entryEval5_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_4 (GramNormalization.eval B) = GramFunctions.Block3.form5.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck5_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form5 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_4]

def rows5_5 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7754, row7755, row7756, row7757, row7758, row7759, row7760, row7761, row7762, row7763, row7764, row7765, row7766, row7767, row7768, row7769, row7770, row7771, row7772, row7773, row7774, row7775, row7776, row7777, row7778, row7779, row7780, row7781, row7782, row7783, row7784, row7785, row7786, row7787, row7788, row7789]

theorem entryCheck5_5 : entry5_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_5 k)) := by decide +kernel

theorem rowsSound5_5 (k : Fin GramFunctions.Block3.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form5.terms k).tag (GramFunctions.Block3.form5.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval7754 x
  · exact rowEval7755 x
  · exact rowEval7756 x
  · exact rowEval7757 x
  · exact rowEval7758 x
  · exact rowEval7759 x
  · exact rowEval7760 x
  · exact rowEval7761 x
  · exact rowEval7762 x
  · exact rowEval7763 x
  · exact rowEval7764 x
  · exact rowEval7765 x
  · exact rowEval7766 x
  · exact rowEval7767 x
  · exact rowEval7768 x
  · exact rowEval7769 x
  · exact rowEval7770 x
  · exact rowEval7771 x
  · exact rowEval7772 x
  · exact rowEval7773 x
  · exact rowEval7774 x
  · exact rowEval7775 x
  · exact rowEval7776 x
  · exact rowEval7777 x
  · exact rowEval7778 x
  · exact rowEval7779 x
  · exact rowEval7780 x
  · exact rowEval7781 x
  · exact rowEval7782 x
  · exact rowEval7783 x
  · exact rowEval7784 x
  · exact rowEval7785 x
  · exact rowEval7786 x
  · exact rowEval7787 x
  · exact rowEval7788 x
  · exact rowEval7789 x

theorem entryEval5_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_5 (GramNormalization.eval B) = GramFunctions.Block3.form5.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck5_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form5 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_5]

end MUB6.Certificate.GramEntries.Block3

end OAI
