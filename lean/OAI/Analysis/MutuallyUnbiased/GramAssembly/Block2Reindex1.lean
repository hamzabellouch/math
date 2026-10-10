import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem entry_reindex_1_0 :
    Integer.Sparse.reindex key entry_1_0 = GramEntries.Block2.entries 1 0 := by
  decide +kernel

theorem entry_reindex_1_1 :
    Integer.Sparse.reindex key entry_1_1 = GramEntries.Block2.entries 1 1 := by
  decide +kernel

theorem entry_reindex_1_2 :
    Integer.Sparse.reindex key entry_1_2 = GramEntries.Block2.entries 1 2 := by
  decide +kernel

theorem entry_reindex_1_3 :
    Integer.Sparse.reindex key entry_1_3 = GramEntries.Block2.entries 1 3 := by
  decide +kernel

theorem entry_reindex_1_4 :
    Integer.Sparse.reindex key entry_1_4 = GramEntries.Block2.entries 1 4 := by
  decide +kernel

theorem entry_reindex_1_5 :
    Integer.Sparse.reindex key entry_1_5 = GramEntries.Block2.entries 1 5 := by
  decide +kernel

theorem entry_reindex_1_6 :
    Integer.Sparse.reindex key entry_1_6 = GramEntries.Block2.entries 1 6 := by
  decide +kernel

theorem entry_reindex_1_7 :
    Integer.Sparse.reindex key entry_1_7 = GramEntries.Block2.entries 1 7 := by
  decide +kernel

theorem entry_reindex_1_8 :
    Integer.Sparse.reindex key entry_1_8 = GramEntries.Block2.entries 1 8 := by
  decide +kernel

theorem entry_reindex_1_9 :
    Integer.Sparse.reindex key entry_1_9 = GramEntries.Block2.entries 1 9 := by
  decide +kernel

theorem entry_reindex_1_10 :
    Integer.Sparse.reindex key entry_1_10 = GramEntries.Block2.entries 1 10 := by
  decide +kernel

theorem entries_reindex_1 (j : Fin 11) :
    Integer.Sparse.reindex key (entries 1 j) = GramEntries.Block2.entries 1 j := by
  fin_cases j
  · exact entry_reindex_1_0
  · exact entry_reindex_1_1
  · exact entry_reindex_1_2
  · exact entry_reindex_1_3
  · exact entry_reindex_1_4
  · exact entry_reindex_1_5
  · exact entry_reindex_1_6
  · exact entry_reindex_1_7
  · exact entry_reindex_1_8
  · exact entry_reindex_1_9
  · exact entry_reindex_1_10

end MUB6.Certificate.GramAssembly.Block2

end OAI
