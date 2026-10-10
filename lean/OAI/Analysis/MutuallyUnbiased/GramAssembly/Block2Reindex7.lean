import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem entry_reindex_7_0 :
    Integer.Sparse.reindex key entry_7_0 = GramEntries.Block2.entries 7 0 := by
  decide +kernel

theorem entry_reindex_7_1 :
    Integer.Sparse.reindex key entry_7_1 = GramEntries.Block2.entries 7 1 := by
  decide +kernel

theorem entry_reindex_7_2 :
    Integer.Sparse.reindex key entry_7_2 = GramEntries.Block2.entries 7 2 := by
  decide +kernel

theorem entry_reindex_7_3 :
    Integer.Sparse.reindex key entry_7_3 = GramEntries.Block2.entries 7 3 := by
  decide +kernel

theorem entry_reindex_7_4 :
    Integer.Sparse.reindex key entry_7_4 = GramEntries.Block2.entries 7 4 := by
  decide +kernel

theorem entry_reindex_7_5 :
    Integer.Sparse.reindex key entry_7_5 = GramEntries.Block2.entries 7 5 := by
  decide +kernel

theorem entry_reindex_7_6 :
    Integer.Sparse.reindex key entry_7_6 = GramEntries.Block2.entries 7 6 := by
  decide +kernel

theorem entry_reindex_7_7 :
    Integer.Sparse.reindex key entry_7_7 = GramEntries.Block2.entries 7 7 := by
  decide +kernel

theorem entry_reindex_7_8 :
    Integer.Sparse.reindex key entry_7_8 = GramEntries.Block2.entries 7 8 := by
  decide +kernel

theorem entry_reindex_7_9 :
    Integer.Sparse.reindex key entry_7_9 = GramEntries.Block2.entries 7 9 := by
  decide +kernel

theorem entry_reindex_7_10 :
    Integer.Sparse.reindex key entry_7_10 = GramEntries.Block2.entries 7 10 := by
  decide +kernel

theorem entries_reindex_7 (j : Fin 11) :
    Integer.Sparse.reindex key (entries 7 j) = GramEntries.Block2.entries 7 j := by
  fin_cases j
  · exact entry_reindex_7_0
  · exact entry_reindex_7_1
  · exact entry_reindex_7_2
  · exact entry_reindex_7_3
  · exact entry_reindex_7_4
  · exact entry_reindex_7_5
  · exact entry_reindex_7_6
  · exact entry_reindex_7_7
  · exact entry_reindex_7_8
  · exact entry_reindex_7_9
  · exact entry_reindex_7_10

end MUB6.Certificate.GramAssembly.Block2

end OAI
