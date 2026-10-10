import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block127

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block4.form1.size → Integer.Sparse Key := ![row13205, row13206, row13207, row13208, row13209, row13210, row13211, row13212, row13213, row13214, row13215, row13216, row13217, row13218, row13219, row13220, row13221, row13222, row13223, row13224]

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block4.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form1.terms k).tag (GramFunctions.Block4.form1.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13205 x
  · exact rowEval13206 x
  · exact rowEval13207 x
  · exact rowEval13208 x
  · exact rowEval13209 x
  · exact rowEval13210 x
  · exact rowEval13211 x
  · exact rowEval13212 x
  · exact rowEval13213 x
  · exact rowEval13214 x
  · exact rowEval13215 x
  · exact rowEval13216 x
  · exact rowEval13217 x
  · exact rowEval13218 x
  · exact rowEval13219 x
  · exact rowEval13220 x
  · exact rowEval13221 x
  · exact rowEval13222 x
  · exact rowEval13223 x
  · exact rowEval13224 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block4.form1.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form1 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

def rows1_1 : Fin GramFunctions.Block4.form1.size → Integer.Sparse Key := ![row13225, row13226, row13227, row13228, row13229, row13230, row13231, row13232, row13233, row13234, row13235, row13236, row13237, row13238, row13239, row13240, row13241, row13242, row13243, row13244]

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block4.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form1.terms k).tag (GramFunctions.Block4.form1.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13225 x
  · exact rowEval13226 x
  · exact rowEval13227 x
  · exact rowEval13228 x
  · exact rowEval13229 x
  · exact rowEval13230 x
  · exact rowEval13231 x
  · exact rowEval13232 x
  · exact rowEval13233 x
  · exact rowEval13234 x
  · exact rowEval13235 x
  · exact rowEval13236 x
  · exact rowEval13237 x
  · exact rowEval13238 x
  · exact rowEval13239 x
  · exact rowEval13240 x
  · exact rowEval13241 x
  · exact rowEval13242 x
  · exact rowEval13243 x
  · exact rowEval13244 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block4.form1.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form1 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

end MUB6.Certificate.GramEntries.Block4

end OAI
