import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block68
import OAI.Analysis.MutuallyUnbiased.GramRows.Block69
import OAI.Analysis.MutuallyUnbiased.GramRows.Block70

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5658, row5659, row5660, row5661, row5662, row5663, row5664, row5665, row5666, row5667, row5668, row5669, row5670, row5671, row5672, row5673, row5674, row5675, row5676, row5677, row5678, row5679, row5680, row5681, row5682, row5683, row5684, row5685, row5686, row5687, row5688, row5689, row5690, row5691, row5692, row5693, row5694, row5695, row5696, row5697]

theorem entryCheck5_0 : entry5_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form5.terms k).coefficient) (rows5_0 k)) := by decide +kernel

theorem rowsSound5_0 (k : Fin GramFunctions.Block2.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form5.terms k).tag (GramFunctions.Block2.form5.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval5658 x
  · exact rowEval5659 x
  · exact rowEval5660 x
  · exact rowEval5661 x
  · exact rowEval5662 x
  · exact rowEval5663 x
  · exact rowEval5664 x
  · exact rowEval5665 x
  · exact rowEval5666 x
  · exact rowEval5667 x
  · exact rowEval5668 x
  · exact rowEval5669 x
  · exact rowEval5670 x
  · exact rowEval5671 x
  · exact rowEval5672 x
  · exact rowEval5673 x
  · exact rowEval5674 x
  · exact rowEval5675 x
  · exact rowEval5676 x
  · exact rowEval5677 x
  · exact rowEval5678 x
  · exact rowEval5679 x
  · exact rowEval5680 x
  · exact rowEval5681 x
  · exact rowEval5682 x
  · exact rowEval5683 x
  · exact rowEval5684 x
  · exact rowEval5685 x
  · exact rowEval5686 x
  · exact rowEval5687 x
  · exact rowEval5688 x
  · exact rowEval5689 x
  · exact rowEval5690 x
  · exact rowEval5691 x
  · exact rowEval5692 x
  · exact rowEval5693 x
  · exact rowEval5694 x
  · exact rowEval5695 x
  · exact rowEval5696 x
  · exact rowEval5697 x

theorem entryEval5_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_0 (GramNormalization.eval B) = GramFunctions.Block2.form5.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck5_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form5 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_0]

def rows5_1 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5698, row5699, row5700, row5701, row5702, row5703, row5704, row5705, row5706, row5707, row5708, row5709, row5710, row5711, row5712, row5713, row5714, row5715, row5716, row5717, row5718, row5719, row5720, row5721, row5722, row5723, row5724, row5725, row5726, row5727, row5728, row5729, row5730, row5731, row5732, row5733, row5734, row5735, row5736, row5737]

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block2.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form5.terms k).tag (GramFunctions.Block2.form5.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval5698 x
  · exact rowEval5699 x
  · exact rowEval5700 x
  · exact rowEval5701 x
  · exact rowEval5702 x
  · exact rowEval5703 x
  · exact rowEval5704 x
  · exact rowEval5705 x
  · exact rowEval5706 x
  · exact rowEval5707 x
  · exact rowEval5708 x
  · exact rowEval5709 x
  · exact rowEval5710 x
  · exact rowEval5711 x
  · exact rowEval5712 x
  · exact rowEval5713 x
  · exact rowEval5714 x
  · exact rowEval5715 x
  · exact rowEval5716 x
  · exact rowEval5717 x
  · exact rowEval5718 x
  · exact rowEval5719 x
  · exact rowEval5720 x
  · exact rowEval5721 x
  · exact rowEval5722 x
  · exact rowEval5723 x
  · exact rowEval5724 x
  · exact rowEval5725 x
  · exact rowEval5726 x
  · exact rowEval5727 x
  · exact rowEval5728 x
  · exact rowEval5729 x
  · exact rowEval5730 x
  · exact rowEval5731 x
  · exact rowEval5732 x
  · exact rowEval5733 x
  · exact rowEval5734 x
  · exact rowEval5735 x
  · exact rowEval5736 x
  · exact rowEval5737 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block2.form5.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form5 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

def rows5_2 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5738, row5739, row5740, row5741, row5742, row5743, row5744, row5745, row5746, row5747, row5748, row5749, row5750, row5751, row5752, row5753, row5754, row5755, row5756, row5757, row5758, row5759, row5760, row5761, row5762, row5763, row5764, row5765, row5766, row5767, row5768, row5769, row5770, row5771, row5772, row5773, row5774, row5775, row5776, row5777]

theorem entryCheck5_2 : entry5_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form5.terms k).coefficient) (rows5_2 k)) := by decide +kernel

theorem rowsSound5_2 (k : Fin GramFunctions.Block2.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form5.terms k).tag (GramFunctions.Block2.form5.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval5738 x
  · exact rowEval5739 x
  · exact rowEval5740 x
  · exact rowEval5741 x
  · exact rowEval5742 x
  · exact rowEval5743 x
  · exact rowEval5744 x
  · exact rowEval5745 x
  · exact rowEval5746 x
  · exact rowEval5747 x
  · exact rowEval5748 x
  · exact rowEval5749 x
  · exact rowEval5750 x
  · exact rowEval5751 x
  · exact rowEval5752 x
  · exact rowEval5753 x
  · exact rowEval5754 x
  · exact rowEval5755 x
  · exact rowEval5756 x
  · exact rowEval5757 x
  · exact rowEval5758 x
  · exact rowEval5759 x
  · exact rowEval5760 x
  · exact rowEval5761 x
  · exact rowEval5762 x
  · exact rowEval5763 x
  · exact rowEval5764 x
  · exact rowEval5765 x
  · exact rowEval5766 x
  · exact rowEval5767 x
  · exact rowEval5768 x
  · exact rowEval5769 x
  · exact rowEval5770 x
  · exact rowEval5771 x
  · exact rowEval5772 x
  · exact rowEval5773 x
  · exact rowEval5774 x
  · exact rowEval5775 x
  · exact rowEval5776 x
  · exact rowEval5777 x

theorem entryEval5_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_2 (GramNormalization.eval B) = GramFunctions.Block2.form5.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck5_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form5 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_2]

def rows5_3 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5778, row5779, row5780, row5781, row5782, row5783, row5784, row5785, row5786, row5787, row5788, row5789, row5790, row5791, row5792, row5793, row5794, row5795, row5796, row5797, row5798, row5799, row5800, row5801, row5802, row5803, row5804, row5805, row5806, row5807, row5808, row5809, row5810, row5811, row5812, row5813, row5814, row5815, row5816, row5817]

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block2.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form5.terms k).tag (GramFunctions.Block2.form5.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval5778 x
  · exact rowEval5779 x
  · exact rowEval5780 x
  · exact rowEval5781 x
  · exact rowEval5782 x
  · exact rowEval5783 x
  · exact rowEval5784 x
  · exact rowEval5785 x
  · exact rowEval5786 x
  · exact rowEval5787 x
  · exact rowEval5788 x
  · exact rowEval5789 x
  · exact rowEval5790 x
  · exact rowEval5791 x
  · exact rowEval5792 x
  · exact rowEval5793 x
  · exact rowEval5794 x
  · exact rowEval5795 x
  · exact rowEval5796 x
  · exact rowEval5797 x
  · exact rowEval5798 x
  · exact rowEval5799 x
  · exact rowEval5800 x
  · exact rowEval5801 x
  · exact rowEval5802 x
  · exact rowEval5803 x
  · exact rowEval5804 x
  · exact rowEval5805 x
  · exact rowEval5806 x
  · exact rowEval5807 x
  · exact rowEval5808 x
  · exact rowEval5809 x
  · exact rowEval5810 x
  · exact rowEval5811 x
  · exact rowEval5812 x
  · exact rowEval5813 x
  · exact rowEval5814 x
  · exact rowEval5815 x
  · exact rowEval5816 x
  · exact rowEval5817 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block2.form5.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form5 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

def rows5_4 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5818, row5819, row5820, row5821, row5822, row5823, row5824, row5825, row5826, row5827, row5828, row5829, row5830, row5831, row5832, row5833, row5834, row5835, row5836, row5837, row5838, row5839, row5840, row5841, row5842, row5843, row5844, row5845, row5846, row5847, row5848, row5849, row5850, row5851, row5852, row5853, row5854, row5855, row5856, row5857]

theorem entryCheck5_4 : entry5_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form5.terms k).coefficient) (rows5_4 k)) := by decide +kernel

theorem rowsSound5_4 (k : Fin GramFunctions.Block2.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form5.terms k).tag (GramFunctions.Block2.form5.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval5818 x
  · exact rowEval5819 x
  · exact rowEval5820 x
  · exact rowEval5821 x
  · exact rowEval5822 x
  · exact rowEval5823 x
  · exact rowEval5824 x
  · exact rowEval5825 x
  · exact rowEval5826 x
  · exact rowEval5827 x
  · exact rowEval5828 x
  · exact rowEval5829 x
  · exact rowEval5830 x
  · exact rowEval5831 x
  · exact rowEval5832 x
  · exact rowEval5833 x
  · exact rowEval5834 x
  · exact rowEval5835 x
  · exact rowEval5836 x
  · exact rowEval5837 x
  · exact rowEval5838 x
  · exact rowEval5839 x
  · exact rowEval5840 x
  · exact rowEval5841 x
  · exact rowEval5842 x
  · exact rowEval5843 x
  · exact rowEval5844 x
  · exact rowEval5845 x
  · exact rowEval5846 x
  · exact rowEval5847 x
  · exact rowEval5848 x
  · exact rowEval5849 x
  · exact rowEval5850 x
  · exact rowEval5851 x
  · exact rowEval5852 x
  · exact rowEval5853 x
  · exact rowEval5854 x
  · exact rowEval5855 x
  · exact rowEval5856 x
  · exact rowEval5857 x

theorem entryEval5_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_4 (GramNormalization.eval B) = GramFunctions.Block2.form5.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck5_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form5 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_4]

def rows5_5 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5858, row5859, row5860, row5861, row5862, row5863, row5864, row5865, row5866, row5867, row5868, row5869, row5870, row5871, row5872, row5873, row5874, row5875, row5876, row5877, row5878, row5879, row5880, row5881, row5882, row5883, row5884, row5885, row5886, row5887, row5888, row5889, row5890, row5891, row5892, row5893, row5894, row5895, row5896, row5897]

theorem entryCheck5_5 : entry5_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form5.terms k).coefficient) (rows5_5 k)) := by decide +kernel

theorem rowsSound5_5 (k : Fin GramFunctions.Block2.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form5.terms k).tag (GramFunctions.Block2.form5.terms k).charge GramFunctions.Block2.form5) x := by
  fin_cases k
  · exact rowEval5858 x
  · exact rowEval5859 x
  · exact rowEval5860 x
  · exact rowEval5861 x
  · exact rowEval5862 x
  · exact rowEval5863 x
  · exact rowEval5864 x
  · exact rowEval5865 x
  · exact rowEval5866 x
  · exact rowEval5867 x
  · exact rowEval5868 x
  · exact rowEval5869 x
  · exact rowEval5870 x
  · exact rowEval5871 x
  · exact rowEval5872 x
  · exact rowEval5873 x
  · exact rowEval5874 x
  · exact rowEval5875 x
  · exact rowEval5876 x
  · exact rowEval5877 x
  · exact rowEval5878 x
  · exact rowEval5879 x
  · exact rowEval5880 x
  · exact rowEval5881 x
  · exact rowEval5882 x
  · exact rowEval5883 x
  · exact rowEval5884 x
  · exact rowEval5885 x
  · exact rowEval5886 x
  · exact rowEval5887 x
  · exact rowEval5888 x
  · exact rowEval5889 x
  · exact rowEval5890 x
  · exact rowEval5891 x
  · exact rowEval5892 x
  · exact rowEval5893 x
  · exact rowEval5894 x
  · exact rowEval5895 x
  · exact rowEval5896 x
  · exact rowEval5897 x

theorem entryEval5_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_5 (GramNormalization.eval B) = GramFunctions.Block2.form5.mixedGram GramFunctions.Block2.form5 B := by
  rw [entryCheck5_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form5 GramFunctions.Block2.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_5]

end MUB6.Certificate.GramEntries.Block2

end OAI
