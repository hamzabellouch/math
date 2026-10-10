import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem entry_reindex_10_0 :
    Integer.Sparse.reindex key entry_10_0 = GramEntries.Block2.entries 10 0 := by
  decide +kernel

theorem entry_reindex_10_1 :
    Integer.Sparse.reindex key entry_10_1 = GramEntries.Block2.entries 10 1 := by
  decide +kernel

theorem entry_reindex_10_2 :
    Integer.Sparse.reindex key entry_10_2 = GramEntries.Block2.entries 10 2 := by
  decide +kernel

theorem entry_reindex_10_3 :
    Integer.Sparse.reindex key entry_10_3 = GramEntries.Block2.entries 10 3 := by
  decide +kernel

theorem entry_reindex_10_4 :
    Integer.Sparse.reindex key entry_10_4 = GramEntries.Block2.entries 10 4 := by
  decide +kernel

theorem entry_reindex_10_5 :
    Integer.Sparse.reindex key entry_10_5 = GramEntries.Block2.entries 10 5 := by
  decide +kernel

theorem entry_reindex_10_6 :
    Integer.Sparse.reindex key entry_10_6 = GramEntries.Block2.entries 10 6 := by
  decide +kernel

theorem entry_reindex_10_7 :
    Integer.Sparse.reindex key entry_10_7 = GramEntries.Block2.entries 10 7 := by
  decide +kernel

theorem entry_reindex_10_8 :
    Integer.Sparse.reindex key entry_10_8 = GramEntries.Block2.entries 10 8 := by
  decide +kernel

theorem entry_reindex_10_9 :
    Integer.Sparse.reindex key entry_10_9 = GramEntries.Block2.entries 10 9 := by
  decide +kernel

theorem entry_reindex_10_10 :
    Integer.Sparse.reindex key entry_10_10 = GramEntries.Block2.entries 10 10 := by
  decide +kernel

theorem entries_reindex_10 (j : Fin 11) :
    Integer.Sparse.reindex key (entries 10 j) = GramEntries.Block2.entries 10 j := by
  fin_cases j
  · exact entry_reindex_10_0
  · exact entry_reindex_10_1
  · exact entry_reindex_10_2
  · exact entry_reindex_10_3
  · exact entry_reindex_10_4
  · exact entry_reindex_10_5
  · exact entry_reindex_10_6
  · exact entry_reindex_10_7
  · exact entry_reindex_10_8
  · exact entry_reindex_10_9
  · exact entry_reindex_10_10

end MUB6.Certificate.GramAssembly.Block2

end OAI
