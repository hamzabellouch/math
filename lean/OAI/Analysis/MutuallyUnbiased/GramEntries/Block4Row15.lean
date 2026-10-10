import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block134
import OAI.Analysis.MutuallyUnbiased.GramRows.Block135
import OAI.Analysis.MutuallyUnbiased.GramRows.Block136
import OAI.Analysis.MutuallyUnbiased.GramRows.Block137
import OAI.Analysis.MutuallyUnbiased.GramRows.Block138
import OAI.Analysis.MutuallyUnbiased.GramRows.Block146
import OAI.Analysis.MutuallyUnbiased.GramRows.Block147
import OAI.Analysis.MutuallyUnbiased.GramRows.Block148
import OAI.Analysis.MutuallyUnbiased.GramRows.Block149

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows15_0 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15717, row15718, row15719, row15720, row15721, row15722, row15723, row15724, row15725, row14205, row14206, row14207, row14208, row14209, row14210, row14211, row14212, row14213, row15726, row15727, row15728, row15729, row15730, row15731, row14214, row14215, row14216, row14217, row14218, row14219, row15732, row15733, row15734, row14232, row14233, row14234]

theorem entryCheck15_0 : entry15_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_0 k)) := by decide +kernel

theorem rowsSound15_0 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval15717 x
  · exact rowEval15718 x
  · exact rowEval15719 x
  · exact rowEval15720 x
  · exact rowEval15721 x
  · exact rowEval15722 x
  · exact rowEval15723 x
  · exact rowEval15724 x
  · exact rowEval15725 x
  · exact rowEval14205 x
  · exact rowEval14206 x
  · exact rowEval14207 x
  · exact rowEval14208 x
  · exact rowEval14209 x
  · exact rowEval14210 x
  · exact rowEval14211 x
  · exact rowEval14212 x
  · exact rowEval14213 x
  · exact rowEval15726 x
  · exact rowEval15727 x
  · exact rowEval15728 x
  · exact rowEval15729 x
  · exact rowEval15730 x
  · exact rowEval15731 x
  · exact rowEval14214 x
  · exact rowEval14215 x
  · exact rowEval14216 x
  · exact rowEval14217 x
  · exact rowEval14218 x
  · exact rowEval14219 x
  · exact rowEval15732 x
  · exact rowEval15733 x
  · exact rowEval15734 x
  · exact rowEval14232 x
  · exact rowEval14233 x
  · exact rowEval14234 x

theorem entryEval15_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_0 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck15_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_0]

def rows15_1 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15735, row15736, row15737, row15738, row15739, row15740, row15741, row15742, row15743, row14241, row14242, row14243, row14244, row14245, row14246, row14247, row14248, row14249, row15744, row15745, row15746, row15747, row15748, row15749, row14250, row14251, row14252, row14253, row14254, row14255, row15750, row15751, row15752, row14268, row14269, row14270]

theorem entryCheck15_1 : entry15_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_1 k)) := by decide +kernel

theorem rowsSound15_1 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval15735 x
  · exact rowEval15736 x
  · exact rowEval15737 x
  · exact rowEval15738 x
  · exact rowEval15739 x
  · exact rowEval15740 x
  · exact rowEval15741 x
  · exact rowEval15742 x
  · exact rowEval15743 x
  · exact rowEval14241 x
  · exact rowEval14242 x
  · exact rowEval14243 x
  · exact rowEval14244 x
  · exact rowEval14245 x
  · exact rowEval14246 x
  · exact rowEval14247 x
  · exact rowEval14248 x
  · exact rowEval14249 x
  · exact rowEval15744 x
  · exact rowEval15745 x
  · exact rowEval15746 x
  · exact rowEval15747 x
  · exact rowEval15748 x
  · exact rowEval15749 x
  · exact rowEval14250 x
  · exact rowEval14251 x
  · exact rowEval14252 x
  · exact rowEval14253 x
  · exact rowEval14254 x
  · exact rowEval14255 x
  · exact rowEval15750 x
  · exact rowEval15751 x
  · exact rowEval15752 x
  · exact rowEval14268 x
  · exact rowEval14269 x
  · exact rowEval14270 x

theorem entryEval15_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_1 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck15_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_1]

def rows15_2 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15753, row15754, row15755, row15756, row15757, row15758, row15759, row15760, row15761, row14277, row14278, row14279, row14280, row14281, row14282, row14283, row14284, row14285, row15762, row15763, row15764, row15765, row15766, row15767, row14286, row14287, row14288, row14289, row14290, row14291, row15768, row15769, row15770, row14304, row14305, row14306]

theorem entryCheck15_2 : entry15_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_2 k)) := by decide +kernel

theorem rowsSound15_2 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval15753 x
  · exact rowEval15754 x
  · exact rowEval15755 x
  · exact rowEval15756 x
  · exact rowEval15757 x
  · exact rowEval15758 x
  · exact rowEval15759 x
  · exact rowEval15760 x
  · exact rowEval15761 x
  · exact rowEval14277 x
  · exact rowEval14278 x
  · exact rowEval14279 x
  · exact rowEval14280 x
  · exact rowEval14281 x
  · exact rowEval14282 x
  · exact rowEval14283 x
  · exact rowEval14284 x
  · exact rowEval14285 x
  · exact rowEval15762 x
  · exact rowEval15763 x
  · exact rowEval15764 x
  · exact rowEval15765 x
  · exact rowEval15766 x
  · exact rowEval15767 x
  · exact rowEval14286 x
  · exact rowEval14287 x
  · exact rowEval14288 x
  · exact rowEval14289 x
  · exact rowEval14290 x
  · exact rowEval14291 x
  · exact rowEval15768 x
  · exact rowEval15769 x
  · exact rowEval15770 x
  · exact rowEval14304 x
  · exact rowEval14305 x
  · exact rowEval14306 x

theorem entryEval15_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_2 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck15_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_2]

def rows15_3 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15771, row15772, row15773, row15774, row15775, row15776, row15777, row15778, row15779, row14313, row14314, row14315, row14316, row14317, row14318, row14319, row14320, row14321, row15780, row15781, row15782, row15783, row15784, row15785, row14322, row14323, row14324, row14325, row14326, row14327, row15786, row15787, row15788, row14340, row14341, row14342]

theorem entryCheck15_3 : entry15_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_3 k)) := by decide +kernel

theorem rowsSound15_3 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval15771 x
  · exact rowEval15772 x
  · exact rowEval15773 x
  · exact rowEval15774 x
  · exact rowEval15775 x
  · exact rowEval15776 x
  · exact rowEval15777 x
  · exact rowEval15778 x
  · exact rowEval15779 x
  · exact rowEval14313 x
  · exact rowEval14314 x
  · exact rowEval14315 x
  · exact rowEval14316 x
  · exact rowEval14317 x
  · exact rowEval14318 x
  · exact rowEval14319 x
  · exact rowEval14320 x
  · exact rowEval14321 x
  · exact rowEval15780 x
  · exact rowEval15781 x
  · exact rowEval15782 x
  · exact rowEval15783 x
  · exact rowEval15784 x
  · exact rowEval15785 x
  · exact rowEval14322 x
  · exact rowEval14323 x
  · exact rowEval14324 x
  · exact rowEval14325 x
  · exact rowEval14326 x
  · exact rowEval14327 x
  · exact rowEval15786 x
  · exact rowEval15787 x
  · exact rowEval15788 x
  · exact rowEval14340 x
  · exact rowEval14341 x
  · exact rowEval14342 x

theorem entryEval15_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_3 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck15_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_3]

def rows15_4 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15789, row15790, row15791, row15792, row15793, row15794, row15795, row15796, row15797, row14349, row14350, row14351, row14352, row14353, row14354, row14355, row14356, row14357, row15798, row15799, row15800, row15801, row15802, row15803, row14358, row14359, row14360, row14361, row14362, row14363, row15804, row15805, row15806, row14376, row14377, row14378]

theorem entryCheck15_4 : entry15_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_4 k)) := by decide +kernel

theorem rowsSound15_4 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval15789 x
  · exact rowEval15790 x
  · exact rowEval15791 x
  · exact rowEval15792 x
  · exact rowEval15793 x
  · exact rowEval15794 x
  · exact rowEval15795 x
  · exact rowEval15796 x
  · exact rowEval15797 x
  · exact rowEval14349 x
  · exact rowEval14350 x
  · exact rowEval14351 x
  · exact rowEval14352 x
  · exact rowEval14353 x
  · exact rowEval14354 x
  · exact rowEval14355 x
  · exact rowEval14356 x
  · exact rowEval14357 x
  · exact rowEval15798 x
  · exact rowEval15799 x
  · exact rowEval15800 x
  · exact rowEval15801 x
  · exact rowEval15802 x
  · exact rowEval15803 x
  · exact rowEval14358 x
  · exact rowEval14359 x
  · exact rowEval14360 x
  · exact rowEval14361 x
  · exact rowEval14362 x
  · exact rowEval14363 x
  · exact rowEval15804 x
  · exact rowEval15805 x
  · exact rowEval15806 x
  · exact rowEval14376 x
  · exact rowEval14377 x
  · exact rowEval14378 x

theorem entryEval15_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_4 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck15_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_4]

def rows15_5 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15807, row15808, row15809, row15810, row15811, row15812, row15813, row15814, row15815, row14385, row14386, row14387, row14388, row14389, row14390, row14391, row14392, row14393, row15816, row15817, row15818, row15819, row15820, row15821, row14394, row14395, row14396, row14397, row14398, row14399, row15822, row15823, row15824, row14412, row14413, row14414]

theorem entryCheck15_5 : entry15_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_5 k)) := by decide +kernel

theorem rowsSound15_5 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval15807 x
  · exact rowEval15808 x
  · exact rowEval15809 x
  · exact rowEval15810 x
  · exact rowEval15811 x
  · exact rowEval15812 x
  · exact rowEval15813 x
  · exact rowEval15814 x
  · exact rowEval15815 x
  · exact rowEval14385 x
  · exact rowEval14386 x
  · exact rowEval14387 x
  · exact rowEval14388 x
  · exact rowEval14389 x
  · exact rowEval14390 x
  · exact rowEval14391 x
  · exact rowEval14392 x
  · exact rowEval14393 x
  · exact rowEval15816 x
  · exact rowEval15817 x
  · exact rowEval15818 x
  · exact rowEval15819 x
  · exact rowEval15820 x
  · exact rowEval15821 x
  · exact rowEval14394 x
  · exact rowEval14395 x
  · exact rowEval14396 x
  · exact rowEval14397 x
  · exact rowEval14398 x
  · exact rowEval14399 x
  · exact rowEval15822 x
  · exact rowEval15823 x
  · exact rowEval15824 x
  · exact rowEval14412 x
  · exact rowEval14413 x
  · exact rowEval14414 x

theorem entryEval15_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_5 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck15_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_5]

def rows15_6 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15825, row15826, row15827, row15828, row15829, row15830, row15831, row15832, row15833, row14421, row14422, row14423, row14424, row14425, row14426, row14427, row14428, row14429, row15834, row15835, row15836, row15837, row15838, row15839, row14430, row14431, row14432, row14433, row14434, row14435, row15840, row15841, row15842, row14448, row14449, row14450]

theorem entryCheck15_6 : entry15_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_6 k)) := by decide +kernel

theorem rowsSound15_6 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval15825 x
  · exact rowEval15826 x
  · exact rowEval15827 x
  · exact rowEval15828 x
  · exact rowEval15829 x
  · exact rowEval15830 x
  · exact rowEval15831 x
  · exact rowEval15832 x
  · exact rowEval15833 x
  · exact rowEval14421 x
  · exact rowEval14422 x
  · exact rowEval14423 x
  · exact rowEval14424 x
  · exact rowEval14425 x
  · exact rowEval14426 x
  · exact rowEval14427 x
  · exact rowEval14428 x
  · exact rowEval14429 x
  · exact rowEval15834 x
  · exact rowEval15835 x
  · exact rowEval15836 x
  · exact rowEval15837 x
  · exact rowEval15838 x
  · exact rowEval15839 x
  · exact rowEval14430 x
  · exact rowEval14431 x
  · exact rowEval14432 x
  · exact rowEval14433 x
  · exact rowEval14434 x
  · exact rowEval14435 x
  · exact rowEval15840 x
  · exact rowEval15841 x
  · exact rowEval15842 x
  · exact rowEval14448 x
  · exact rowEval14449 x
  · exact rowEval14450 x

theorem entryEval15_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_6 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck15_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_6]

def rows15_7 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15843, row15844, row15845, row15846, row15847, row15848, row15849, row15850, row15851, row14457, row14458, row14459, row14460, row14461, row14462, row14463, row14464, row14465, row15852, row15853, row15854, row15855, row15856, row15857, row14466, row14467, row14468, row14469, row14470, row14471, row15858, row15859, row15860, row14484, row14485, row14486]

theorem entryCheck15_7 : entry15_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_7 k)) := by decide +kernel

theorem rowsSound15_7 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval15843 x
  · exact rowEval15844 x
  · exact rowEval15845 x
  · exact rowEval15846 x
  · exact rowEval15847 x
  · exact rowEval15848 x
  · exact rowEval15849 x
  · exact rowEval15850 x
  · exact rowEval15851 x
  · exact rowEval14457 x
  · exact rowEval14458 x
  · exact rowEval14459 x
  · exact rowEval14460 x
  · exact rowEval14461 x
  · exact rowEval14462 x
  · exact rowEval14463 x
  · exact rowEval14464 x
  · exact rowEval14465 x
  · exact rowEval15852 x
  · exact rowEval15853 x
  · exact rowEval15854 x
  · exact rowEval15855 x
  · exact rowEval15856 x
  · exact rowEval15857 x
  · exact rowEval14466 x
  · exact rowEval14467 x
  · exact rowEval14468 x
  · exact rowEval14469 x
  · exact rowEval14470 x
  · exact rowEval14471 x
  · exact rowEval15858 x
  · exact rowEval15859 x
  · exact rowEval15860 x
  · exact rowEval14484 x
  · exact rowEval14485 x
  · exact rowEval14486 x

theorem entryEval15_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_7 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck15_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_7]

def rows15_8 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15861, row15862, row15863, row15864, row15865, row15866, row15867, row15868, row15869, row14493, row14494, row14495, row14496, row14497, row14498, row14499, row14500, row14501, row15870, row15871, row15872, row15873, row15874, row15875, row14502, row14503, row14504, row14505, row14506, row14507, row15876, row15877, row15878, row14520, row14521, row14522]

theorem entryCheck15_8 : entry15_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_8 k)) := by decide +kernel

theorem rowsSound15_8 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval15861 x
  · exact rowEval15862 x
  · exact rowEval15863 x
  · exact rowEval15864 x
  · exact rowEval15865 x
  · exact rowEval15866 x
  · exact rowEval15867 x
  · exact rowEval15868 x
  · exact rowEval15869 x
  · exact rowEval14493 x
  · exact rowEval14494 x
  · exact rowEval14495 x
  · exact rowEval14496 x
  · exact rowEval14497 x
  · exact rowEval14498 x
  · exact rowEval14499 x
  · exact rowEval14500 x
  · exact rowEval14501 x
  · exact rowEval15870 x
  · exact rowEval15871 x
  · exact rowEval15872 x
  · exact rowEval15873 x
  · exact rowEval15874 x
  · exact rowEval15875 x
  · exact rowEval14502 x
  · exact rowEval14503 x
  · exact rowEval14504 x
  · exact rowEval14505 x
  · exact rowEval14506 x
  · exact rowEval14507 x
  · exact rowEval15876 x
  · exact rowEval15877 x
  · exact rowEval15878 x
  · exact rowEval14520 x
  · exact rowEval14521 x
  · exact rowEval14522 x

theorem entryEval15_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_8 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck15_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_8]

def rows15_9 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15879, row15880, row15881, row15882, row15883, row15884, row15885, row15886, row15887, row14529, row14530, row14531, row14532, row14533, row14534, row14535, row14536, row14537, row15888, row15889, row15890, row15891, row15892, row15893, row14538, row14539, row14540, row14541, row14542, row14543, row15894, row15895, row15896, row14556, row14557, row14558]

theorem entryCheck15_9 : entry15_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_9 k)) := by decide +kernel

theorem rowsSound15_9 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval15879 x
  · exact rowEval15880 x
  · exact rowEval15881 x
  · exact rowEval15882 x
  · exact rowEval15883 x
  · exact rowEval15884 x
  · exact rowEval15885 x
  · exact rowEval15886 x
  · exact rowEval15887 x
  · exact rowEval14529 x
  · exact rowEval14530 x
  · exact rowEval14531 x
  · exact rowEval14532 x
  · exact rowEval14533 x
  · exact rowEval14534 x
  · exact rowEval14535 x
  · exact rowEval14536 x
  · exact rowEval14537 x
  · exact rowEval15888 x
  · exact rowEval15889 x
  · exact rowEval15890 x
  · exact rowEval15891 x
  · exact rowEval15892 x
  · exact rowEval15893 x
  · exact rowEval14538 x
  · exact rowEval14539 x
  · exact rowEval14540 x
  · exact rowEval14541 x
  · exact rowEval14542 x
  · exact rowEval14543 x
  · exact rowEval15894 x
  · exact rowEval15895 x
  · exact rowEval15896 x
  · exact rowEval14556 x
  · exact rowEval14557 x
  · exact rowEval14558 x

theorem entryEval15_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_9 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck15_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_9]

def rows15_10 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15897, row15898, row15899, row15900, row15901, row15902, row15903, row15904, row15905, row14565, row14566, row14567, row14568, row14569, row14570, row14571, row14572, row14573, row15906, row15907, row15908, row15909, row15910, row15911, row14574, row14575, row14576, row14577, row14578, row14579, row15912, row15913, row15914, row14592, row14593, row14594]

theorem entryCheck15_10 : entry15_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_10 k)) := by decide +kernel

theorem rowsSound15_10 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval15897 x
  · exact rowEval15898 x
  · exact rowEval15899 x
  · exact rowEval15900 x
  · exact rowEval15901 x
  · exact rowEval15902 x
  · exact rowEval15903 x
  · exact rowEval15904 x
  · exact rowEval15905 x
  · exact rowEval14565 x
  · exact rowEval14566 x
  · exact rowEval14567 x
  · exact rowEval14568 x
  · exact rowEval14569 x
  · exact rowEval14570 x
  · exact rowEval14571 x
  · exact rowEval14572 x
  · exact rowEval14573 x
  · exact rowEval15906 x
  · exact rowEval15907 x
  · exact rowEval15908 x
  · exact rowEval15909 x
  · exact rowEval15910 x
  · exact rowEval15911 x
  · exact rowEval14574 x
  · exact rowEval14575 x
  · exact rowEval14576 x
  · exact rowEval14577 x
  · exact rowEval14578 x
  · exact rowEval14579 x
  · exact rowEval15912 x
  · exact rowEval15913 x
  · exact rowEval15914 x
  · exact rowEval14592 x
  · exact rowEval14593 x
  · exact rowEval14594 x

theorem entryEval15_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_10 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck15_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_10]

def rows15_11 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15915, row15916, row15917, row15918, row15919, row15920, row15921, row15922, row15923, row15924, row15925, row15926, row15927, row15928, row15929, row15930, row15931, row15932, row15933, row15934, row15935, row15936, row15937, row15938, row15939, row15940, row15941, row15942, row15943, row15944, row15945, row15946, row15947, row15948, row15949, row15950]

theorem entryCheck15_11 : entry15_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_11 k)) := by decide +kernel

theorem rowsSound15_11 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval15915 x
  · exact rowEval15916 x
  · exact rowEval15917 x
  · exact rowEval15918 x
  · exact rowEval15919 x
  · exact rowEval15920 x
  · exact rowEval15921 x
  · exact rowEval15922 x
  · exact rowEval15923 x
  · exact rowEval15924 x
  · exact rowEval15925 x
  · exact rowEval15926 x
  · exact rowEval15927 x
  · exact rowEval15928 x
  · exact rowEval15929 x
  · exact rowEval15930 x
  · exact rowEval15931 x
  · exact rowEval15932 x
  · exact rowEval15933 x
  · exact rowEval15934 x
  · exact rowEval15935 x
  · exact rowEval15936 x
  · exact rowEval15937 x
  · exact rowEval15938 x
  · exact rowEval15939 x
  · exact rowEval15940 x
  · exact rowEval15941 x
  · exact rowEval15942 x
  · exact rowEval15943 x
  · exact rowEval15944 x
  · exact rowEval15945 x
  · exact rowEval15946 x
  · exact rowEval15947 x
  · exact rowEval15948 x
  · exact rowEval15949 x
  · exact rowEval15950 x

theorem entryEval15_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_11 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck15_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_11]

def rows15_12 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15951, row15952, row15953, row15954, row15955, row15956, row15957, row15958, row15959, row15960, row15961, row15962, row15963, row15964, row15965, row15966, row15967, row15968, row15969, row15970, row15971, row15972, row15973, row15974, row15975, row15976, row15977, row15978, row15979, row15980, row15981, row15982, row15983, row15984, row15985, row15986]

theorem entryCheck15_12 : entry15_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_12 k)) := by decide +kernel

theorem rowsSound15_12 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval15951 x
  · exact rowEval15952 x
  · exact rowEval15953 x
  · exact rowEval15954 x
  · exact rowEval15955 x
  · exact rowEval15956 x
  · exact rowEval15957 x
  · exact rowEval15958 x
  · exact rowEval15959 x
  · exact rowEval15960 x
  · exact rowEval15961 x
  · exact rowEval15962 x
  · exact rowEval15963 x
  · exact rowEval15964 x
  · exact rowEval15965 x
  · exact rowEval15966 x
  · exact rowEval15967 x
  · exact rowEval15968 x
  · exact rowEval15969 x
  · exact rowEval15970 x
  · exact rowEval15971 x
  · exact rowEval15972 x
  · exact rowEval15973 x
  · exact rowEval15974 x
  · exact rowEval15975 x
  · exact rowEval15976 x
  · exact rowEval15977 x
  · exact rowEval15978 x
  · exact rowEval15979 x
  · exact rowEval15980 x
  · exact rowEval15981 x
  · exact rowEval15982 x
  · exact rowEval15983 x
  · exact rowEval15984 x
  · exact rowEval15985 x
  · exact rowEval15986 x

theorem entryEval15_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_12 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck15_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_12]

def rows15_13 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15987, row15988, row15989, row15990, row15991, row15992, row15993, row15994, row15995, row15996, row15997, row15998, row15999, row16000, row16001, row16002, row16003, row16004, row16005, row16006, row16007, row16008, row16009, row16010, row16011, row16012, row16013, row16014, row16015, row16016, row16017, row16018, row16019, row16020, row16021, row16022]

theorem entryCheck15_13 : entry15_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_13 k)) := by decide +kernel

theorem rowsSound15_13 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval15987 x
  · exact rowEval15988 x
  · exact rowEval15989 x
  · exact rowEval15990 x
  · exact rowEval15991 x
  · exact rowEval15992 x
  · exact rowEval15993 x
  · exact rowEval15994 x
  · exact rowEval15995 x
  · exact rowEval15996 x
  · exact rowEval15997 x
  · exact rowEval15998 x
  · exact rowEval15999 x
  · exact rowEval16000 x
  · exact rowEval16001 x
  · exact rowEval16002 x
  · exact rowEval16003 x
  · exact rowEval16004 x
  · exact rowEval16005 x
  · exact rowEval16006 x
  · exact rowEval16007 x
  · exact rowEval16008 x
  · exact rowEval16009 x
  · exact rowEval16010 x
  · exact rowEval16011 x
  · exact rowEval16012 x
  · exact rowEval16013 x
  · exact rowEval16014 x
  · exact rowEval16015 x
  · exact rowEval16016 x
  · exact rowEval16017 x
  · exact rowEval16018 x
  · exact rowEval16019 x
  · exact rowEval16020 x
  · exact rowEval16021 x
  · exact rowEval16022 x

theorem entryEval15_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_13 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck15_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_13]

def rows15_14 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row16023, row16024, row16025, row16026, row16027, row16028, row16029, row16030, row16031, row16032, row16033, row16034, row16035, row16036, row16037, row16038, row16039, row16040, row16041, row16042, row16043, row16044, row16045, row16046, row16047, row16048, row16049, row16050, row16051, row16052, row16053, row16054, row16055, row16056, row16057, row16058]

theorem entryCheck15_14 : entry15_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_14 k)) := by decide +kernel

theorem rowsSound15_14 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form14) x := by
  fin_cases k
  · exact rowEval16023 x
  · exact rowEval16024 x
  · exact rowEval16025 x
  · exact rowEval16026 x
  · exact rowEval16027 x
  · exact rowEval16028 x
  · exact rowEval16029 x
  · exact rowEval16030 x
  · exact rowEval16031 x
  · exact rowEval16032 x
  · exact rowEval16033 x
  · exact rowEval16034 x
  · exact rowEval16035 x
  · exact rowEval16036 x
  · exact rowEval16037 x
  · exact rowEval16038 x
  · exact rowEval16039 x
  · exact rowEval16040 x
  · exact rowEval16041 x
  · exact rowEval16042 x
  · exact rowEval16043 x
  · exact rowEval16044 x
  · exact rowEval16045 x
  · exact rowEval16046 x
  · exact rowEval16047 x
  · exact rowEval16048 x
  · exact rowEval16049 x
  · exact rowEval16050 x
  · exact rowEval16051 x
  · exact rowEval16052 x
  · exact rowEval16053 x
  · exact rowEval16054 x
  · exact rowEval16055 x
  · exact rowEval16056 x
  · exact rowEval16057 x
  · exact rowEval16058 x

theorem entryEval15_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_14 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form14 B := by
  rw [entryCheck15_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_14]

def rows15_15 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row16059, row16060, row16061, row16062, row16063, row16064, row16065, row16066, row16067, row16068, row16069, row16070, row16071, row16072, row16073, row16074, row16075, row16076, row16077, row16078, row16079, row16080, row16081, row16082, row16083, row16084, row16085, row16086, row16087, row16088, row16089, row16090, row16091, row16092, row16093, row16094]

theorem entryCheck15_15 : entry15_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form15.terms k).coefficient) (rows15_15 k)) := by decide +kernel

theorem rowsSound15_15 (k : Fin GramFunctions.Block4.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form15.terms k).tag (GramFunctions.Block4.form15.terms k).charge GramFunctions.Block4.form15) x := by
  fin_cases k
  · exact rowEval16059 x
  · exact rowEval16060 x
  · exact rowEval16061 x
  · exact rowEval16062 x
  · exact rowEval16063 x
  · exact rowEval16064 x
  · exact rowEval16065 x
  · exact rowEval16066 x
  · exact rowEval16067 x
  · exact rowEval16068 x
  · exact rowEval16069 x
  · exact rowEval16070 x
  · exact rowEval16071 x
  · exact rowEval16072 x
  · exact rowEval16073 x
  · exact rowEval16074 x
  · exact rowEval16075 x
  · exact rowEval16076 x
  · exact rowEval16077 x
  · exact rowEval16078 x
  · exact rowEval16079 x
  · exact rowEval16080 x
  · exact rowEval16081 x
  · exact rowEval16082 x
  · exact rowEval16083 x
  · exact rowEval16084 x
  · exact rowEval16085 x
  · exact rowEval16086 x
  · exact rowEval16087 x
  · exact rowEval16088 x
  · exact rowEval16089 x
  · exact rowEval16090 x
  · exact rowEval16091 x
  · exact rowEval16092 x
  · exact rowEval16093 x
  · exact rowEval16094 x

theorem entryEval15_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_15 (GramNormalization.eval B) = GramFunctions.Block4.form15.mixedGram GramFunctions.Block4.form15 B := by
  rw [entryCheck15_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form15 GramFunctions.Block4.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_15]

end MUB6.Certificate.GramEntries.Block4

end OAI
