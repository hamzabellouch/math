import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem entry_reindex_9_0 :
    Integer.Sparse.reindex key entry_9_0 = GramEntries.Block2.entries 9 0 := by
  decide +kernel

theorem entry_reindex_9_1 :
    Integer.Sparse.reindex key entry_9_1 = GramEntries.Block2.entries 9 1 := by
  decide +kernel

theorem entry_reindex_9_2 :
    Integer.Sparse.reindex key entry_9_2 = GramEntries.Block2.entries 9 2 := by
  decide +kernel

theorem entry_reindex_9_3 :
    Integer.Sparse.reindex key entry_9_3 = GramEntries.Block2.entries 9 3 := by
  decide +kernel

theorem entry_reindex_9_4 :
    Integer.Sparse.reindex key entry_9_4 = GramEntries.Block2.entries 9 4 := by
  decide +kernel

theorem entry_reindex_9_5 :
    Integer.Sparse.reindex key entry_9_5 = GramEntries.Block2.entries 9 5 := by
  decide +kernel

theorem entry_reindex_9_6 :
    Integer.Sparse.reindex key entry_9_6 = GramEntries.Block2.entries 9 6 := by
  decide +kernel

theorem entry_reindex_9_7 :
    Integer.Sparse.reindex key entry_9_7 = GramEntries.Block2.entries 9 7 := by
  decide +kernel

theorem entry_reindex_9_8 :
    Integer.Sparse.reindex key entry_9_8 = GramEntries.Block2.entries 9 8 := by
  decide +kernel

theorem entry_reindex_9_9 :
    Integer.Sparse.reindex key entry_9_9 = GramEntries.Block2.entries 9 9 := by
  decide +kernel

theorem entry_reindex_9_10 :
    Integer.Sparse.reindex key entry_9_10 = GramEntries.Block2.entries 9 10 := by
  decide +kernel

theorem entries_reindex_9 (j : Fin 11) :
    Integer.Sparse.reindex key (entries 9 j) = GramEntries.Block2.entries 9 j := by
  fin_cases j
  · exact entry_reindex_9_0
  · exact entry_reindex_9_1
  · exact entry_reindex_9_2
  · exact entry_reindex_9_3
  · exact entry_reindex_9_4
  · exact entry_reindex_9_5
  · exact entry_reindex_9_6
  · exact entry_reindex_9_7
  · exact entry_reindex_9_8
  · exact entry_reindex_9_9
  · exact entry_reindex_9_10

end MUB6.Certificate.GramAssembly.Block2

end OAI
