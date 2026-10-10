import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block18
import OAI.Analysis.MutuallyUnbiased.GramRows.Block19
import OAI.Analysis.MutuallyUnbiased.GramRows.Block20
import OAI.Analysis.MutuallyUnbiased.GramRows.Block21

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block1.form2.size → Integer.Sparse Key := ![row688, row689, row690, row691, row692, row693, row694, row695, row696, row697, row698, row699, row700, row701, row702, row703, row704, row705, row706, row707, row708, row709, row710, row711, row712, row713, row714, row715, row716, row717]

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block1.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form2.terms k).tag (GramFunctions.Block1.form2.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval688 x
  · exact rowEval689 x
  · exact rowEval690 x
  · exact rowEval691 x
  · exact rowEval692 x
  · exact rowEval693 x
  · exact rowEval694 x
  · exact rowEval695 x
  · exact rowEval696 x
  · exact rowEval697 x
  · exact rowEval698 x
  · exact rowEval699 x
  · exact rowEval700 x
  · exact rowEval701 x
  · exact rowEval702 x
  · exact rowEval703 x
  · exact rowEval704 x
  · exact rowEval705 x
  · exact rowEval706 x
  · exact rowEval707 x
  · exact rowEval708 x
  · exact rowEval709 x
  · exact rowEval710 x
  · exact rowEval711 x
  · exact rowEval712 x
  · exact rowEval713 x
  · exact rowEval714 x
  · exact rowEval715 x
  · exact rowEval716 x
  · exact rowEval717 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block1.form2.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form2 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

def rows2_1 : Fin GramFunctions.Block1.form2.size → Integer.Sparse Key := ![row718, row719, row720, row721, row722, row723, row724, row725, row726, row727, row728, row729, row730, row731, row732, row733, row734, row735, row736, row737, row738, row739, row740, row741, row742, row743, row744, row745, row746, row747]

theorem entryCheck2_1 : entry2_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form2.terms k).coefficient) (rows2_1 k)) := by decide +kernel

theorem rowsSound2_1 (k : Fin GramFunctions.Block1.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form2.terms k).tag (GramFunctions.Block1.form2.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval718 x
  · exact rowEval719 x
  · exact rowEval720 x
  · exact rowEval721 x
  · exact rowEval722 x
  · exact rowEval723 x
  · exact rowEval724 x
  · exact rowEval725 x
  · exact rowEval726 x
  · exact rowEval727 x
  · exact rowEval728 x
  · exact rowEval729 x
  · exact rowEval730 x
  · exact rowEval731 x
  · exact rowEval732 x
  · exact rowEval733 x
  · exact rowEval734 x
  · exact rowEval735 x
  · exact rowEval736 x
  · exact rowEval737 x
  · exact rowEval738 x
  · exact rowEval739 x
  · exact rowEval740 x
  · exact rowEval741 x
  · exact rowEval742 x
  · exact rowEval743 x
  · exact rowEval744 x
  · exact rowEval745 x
  · exact rowEval746 x
  · exact rowEval747 x

theorem entryEval2_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_1 (GramNormalization.eval B) = GramFunctions.Block1.form2.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck2_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form2 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_1]

def rows2_2 : Fin GramFunctions.Block1.form2.size → Integer.Sparse Key := ![row748, row749, row750, row751, row752, row753, row754, row755, row756, row757, row758, row759, row760, row761, row762, row763, row764, row765, row766, row767, row768, row769, row770, row771, row772, row773, row774, row775, row776, row777]

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block1.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form2.terms k).tag (GramFunctions.Block1.form2.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval748 x
  · exact rowEval749 x
  · exact rowEval750 x
  · exact rowEval751 x
  · exact rowEval752 x
  · exact rowEval753 x
  · exact rowEval754 x
  · exact rowEval755 x
  · exact rowEval756 x
  · exact rowEval757 x
  · exact rowEval758 x
  · exact rowEval759 x
  · exact rowEval760 x
  · exact rowEval761 x
  · exact rowEval762 x
  · exact rowEval763 x
  · exact rowEval764 x
  · exact rowEval765 x
  · exact rowEval766 x
  · exact rowEval767 x
  · exact rowEval768 x
  · exact rowEval769 x
  · exact rowEval770 x
  · exact rowEval771 x
  · exact rowEval772 x
  · exact rowEval773 x
  · exact rowEval774 x
  · exact rowEval775 x
  · exact rowEval776 x
  · exact rowEval777 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block1.form2.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form2 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

end MUB6.Certificate.GramEntries.Block1

end OAI
