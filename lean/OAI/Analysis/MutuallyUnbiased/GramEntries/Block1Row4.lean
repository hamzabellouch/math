import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block23
import OAI.Analysis.MutuallyUnbiased.GramRows.Block24
import OAI.Analysis.MutuallyUnbiased.GramRows.Block25

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row834, row835, row836, row837, row838, row839, row840, row841, row842, row843, row844, row845, row846, row847]

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval834 x
  · exact rowEval835 x
  · exact rowEval836 x
  · exact rowEval837 x
  · exact rowEval838 x
  · exact rowEval839 x
  · exact rowEval840 x
  · exact rowEval841 x
  · exact rowEval842 x
  · exact rowEval843 x
  · exact rowEval844 x
  · exact rowEval845 x
  · exact rowEval846 x
  · exact rowEval847 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

def rows4_1 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row848, row849, row850, row851, row852, row853, row854, row855, row856, row857, row858, row859, row860, row861]

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval848 x
  · exact rowEval849 x
  · exact rowEval850 x
  · exact rowEval851 x
  · exact rowEval852 x
  · exact rowEval853 x
  · exact rowEval854 x
  · exact rowEval855 x
  · exact rowEval856 x
  · exact rowEval857 x
  · exact rowEval858 x
  · exact rowEval859 x
  · exact rowEval860 x
  · exact rowEval861 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

def rows4_2 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row862, row863, row864, row865, row866, row867, row868, row869, row870, row871, row872, row873, row874, row875]

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval862 x
  · exact rowEval863 x
  · exact rowEval864 x
  · exact rowEval865 x
  · exact rowEval866 x
  · exact rowEval867 x
  · exact rowEval868 x
  · exact rowEval869 x
  · exact rowEval870 x
  · exact rowEval871 x
  · exact rowEval872 x
  · exact rowEval873 x
  · exact rowEval874 x
  · exact rowEval875 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

def rows4_3 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row876, row877, row878, row879, row880, row881, row882, row883, row884, row885, row886, row887, row888, row889]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval876 x
  · exact rowEval877 x
  · exact rowEval878 x
  · exact rowEval879 x
  · exact rowEval880 x
  · exact rowEval881 x
  · exact rowEval882 x
  · exact rowEval883 x
  · exact rowEval884 x
  · exact rowEval885 x
  · exact rowEval886 x
  · exact rowEval887 x
  · exact rowEval888 x
  · exact rowEval889 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

def rows4_4 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row890, row891, row892, row893, row894, row895, row896, row897, row898, row899, row900, row901, row902, row903]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval890 x
  · exact rowEval891 x
  · exact rowEval892 x
  · exact rowEval893 x
  · exact rowEval894 x
  · exact rowEval895 x
  · exact rowEval896 x
  · exact rowEval897 x
  · exact rowEval898 x
  · exact rowEval899 x
  · exact rowEval900 x
  · exact rowEval901 x
  · exact rowEval902 x
  · exact rowEval903 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block1

end OAI
