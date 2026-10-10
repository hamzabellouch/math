import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramRows.Block0

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block0.form1.size → Integer.Sparse Key := ![row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59, row60, row61, row62, row63, row64, row65, row66, row67, row68, row69, row70, row71, row72, row73, row74, row75, row76, row77, row78, row79, row80, row81, row82, row83]

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block0.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form1.terms k).tag (GramFunctions.Block0.form1.terms k).charge GramFunctions.Block0.form0) x := by
  fin_cases k
  · exact rowEval42 x
  · exact rowEval43 x
  · exact rowEval44 x
  · exact rowEval45 x
  · exact rowEval46 x
  · exact rowEval47 x
  · exact rowEval48 x
  · exact rowEval49 x
  · exact rowEval50 x
  · exact rowEval51 x
  · exact rowEval52 x
  · exact rowEval53 x
  · exact rowEval54 x
  · exact rowEval55 x
  · exact rowEval56 x
  · exact rowEval57 x
  · exact rowEval58 x
  · exact rowEval59 x
  · exact rowEval60 x
  · exact rowEval61 x
  · exact rowEval62 x
  · exact rowEval63 x
  · exact rowEval64 x
  · exact rowEval65 x
  · exact rowEval66 x
  · exact rowEval67 x
  · exact rowEval68 x
  · exact rowEval69 x
  · exact rowEval70 x
  · exact rowEval71 x
  · exact rowEval72 x
  · exact rowEval73 x
  · exact rowEval74 x
  · exact rowEval75 x
  · exact rowEval76 x
  · exact rowEval77 x
  · exact rowEval78 x
  · exact rowEval79 x
  · exact rowEval80 x
  · exact rowEval81 x
  · exact rowEval82 x
  · exact rowEval83 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block0.form1.mixedGram GramFunctions.Block0.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form1 GramFunctions.Block0.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

def rows1_1 : Fin GramFunctions.Block0.form1.size → Integer.Sparse Key := ![row84, row85, row86, row87, row88, row89, row90, row91, row92, row93, row94, row95, row96, row97, row98, row99, row100, row101, row102, row103, row104, row105, row106, row107, row108, row109, row110, row111, row112, row113, row114, row115, row116, row117, row118, row119, row120, row121, row122, row123, row124, row125]

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block0.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form1.terms k).tag (GramFunctions.Block0.form1.terms k).charge GramFunctions.Block0.form1) x := by
  fin_cases k
  · exact rowEval84 x
  · exact rowEval85 x
  · exact rowEval86 x
  · exact rowEval87 x
  · exact rowEval88 x
  · exact rowEval89 x
  · exact rowEval90 x
  · exact rowEval91 x
  · exact rowEval92 x
  · exact rowEval93 x
  · exact rowEval94 x
  · exact rowEval95 x
  · exact rowEval96 x
  · exact rowEval97 x
  · exact rowEval98 x
  · exact rowEval99 x
  · exact rowEval100 x
  · exact rowEval101 x
  · exact rowEval102 x
  · exact rowEval103 x
  · exact rowEval104 x
  · exact rowEval105 x
  · exact rowEval106 x
  · exact rowEval107 x
  · exact rowEval108 x
  · exact rowEval109 x
  · exact rowEval110 x
  · exact rowEval111 x
  · exact rowEval112 x
  · exact rowEval113 x
  · exact rowEval114 x
  · exact rowEval115 x
  · exact rowEval116 x
  · exact rowEval117 x
  · exact rowEval118 x
  · exact rowEval119 x
  · exact rowEval120 x
  · exact rowEval121 x
  · exact rowEval122 x
  · exact rowEval123 x
  · exact rowEval124 x
  · exact rowEval125 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block0.form1.mixedGram GramFunctions.Block0.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form1 GramFunctions.Block0.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

end MUB6.Certificate.GramEntries.Block0

end OAI
