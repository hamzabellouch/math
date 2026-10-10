import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block169
import OAI.Analysis.MutuallyUnbiased.GramRows.Block170

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18659, row18660, row18661, row18662, row18663, row18664, row18665, row18666, row18667, row18668, row18669, row18670, row18671, row18672, row18673, row18674, row18675, row18676, row18677, row18678]

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18659 x
  · exact rowEval18660 x
  · exact rowEval18661 x
  · exact rowEval18662 x
  · exact rowEval18663 x
  · exact rowEval18664 x
  · exact rowEval18665 x
  · exact rowEval18666 x
  · exact rowEval18667 x
  · exact rowEval18668 x
  · exact rowEval18669 x
  · exact rowEval18670 x
  · exact rowEval18671 x
  · exact rowEval18672 x
  · exact rowEval18673 x
  · exact rowEval18674 x
  · exact rowEval18675 x
  · exact rowEval18676 x
  · exact rowEval18677 x
  · exact rowEval18678 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

def rows4_1 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18679, row18680, row18681, row18682, row18683, row18684, row18685, row18686, row18687, row18688, row18689, row18690, row18691, row18692, row18693, row18694, row18695, row18696, row18697, row18698]

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18679 x
  · exact rowEval18680 x
  · exact rowEval18681 x
  · exact rowEval18682 x
  · exact rowEval18683 x
  · exact rowEval18684 x
  · exact rowEval18685 x
  · exact rowEval18686 x
  · exact rowEval18687 x
  · exact rowEval18688 x
  · exact rowEval18689 x
  · exact rowEval18690 x
  · exact rowEval18691 x
  · exact rowEval18692 x
  · exact rowEval18693 x
  · exact rowEval18694 x
  · exact rowEval18695 x
  · exact rowEval18696 x
  · exact rowEval18697 x
  · exact rowEval18698 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

def rows4_2 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18699, row18700, row18701, row18702, row18703, row18704, row18705, row18706, row18707, row18708, row18709, row18710, row18711, row18712, row18713, row18714, row18715, row18716, row18717, row18718]

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval18699 x
  · exact rowEval18700 x
  · exact rowEval18701 x
  · exact rowEval18702 x
  · exact rowEval18703 x
  · exact rowEval18704 x
  · exact rowEval18705 x
  · exact rowEval18706 x
  · exact rowEval18707 x
  · exact rowEval18708 x
  · exact rowEval18709 x
  · exact rowEval18710 x
  · exact rowEval18711 x
  · exact rowEval18712 x
  · exact rowEval18713 x
  · exact rowEval18714 x
  · exact rowEval18715 x
  · exact rowEval18716 x
  · exact rowEval18717 x
  · exact rowEval18718 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

def rows4_3 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18719, row18720, row18721, row18722, row18723, row18724, row18725, row18726, row18727, row18728, row18729, row18730, row18731, row18732, row18733, row18734, row18735, row18736, row18737, row18738]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18719 x
  · exact rowEval18720 x
  · exact rowEval18721 x
  · exact rowEval18722 x
  · exact rowEval18723 x
  · exact rowEval18724 x
  · exact rowEval18725 x
  · exact rowEval18726 x
  · exact rowEval18727 x
  · exact rowEval18728 x
  · exact rowEval18729 x
  · exact rowEval18730 x
  · exact rowEval18731 x
  · exact rowEval18732 x
  · exact rowEval18733 x
  · exact rowEval18734 x
  · exact rowEval18735 x
  · exact rowEval18736 x
  · exact rowEval18737 x
  · exact rowEval18738 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

def rows4_4 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18739, row18740, row18741, row18742, row18743, row18744, row18745, row18746, row18747, row18748, row18749, row18750, row18751, row18752, row18753, row18754, row18755, row18756, row18757, row18758]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval18739 x
  · exact rowEval18740 x
  · exact rowEval18741 x
  · exact rowEval18742 x
  · exact rowEval18743 x
  · exact rowEval18744 x
  · exact rowEval18745 x
  · exact rowEval18746 x
  · exact rowEval18747 x
  · exact rowEval18748 x
  · exact rowEval18749 x
  · exact rowEval18750 x
  · exact rowEval18751 x
  · exact rowEval18752 x
  · exact rowEval18753 x
  · exact rowEval18754 x
  · exact rowEval18755 x
  · exact rowEval18756 x
  · exact rowEval18757 x
  · exact rowEval18758 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block5

end OAI
