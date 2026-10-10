import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem entry_reindex_5_0 :
    Integer.Sparse.reindex key entry_5_0 = GramEntries.Block2.entries 5 0 := by
  decide +kernel

theorem entry_reindex_5_1 :
    Integer.Sparse.reindex key entry_5_1 = GramEntries.Block2.entries 5 1 := by
  decide +kernel

theorem entry_reindex_5_2 :
    Integer.Sparse.reindex key entry_5_2 = GramEntries.Block2.entries 5 2 := by
  decide +kernel

theorem entry_reindex_5_3 :
    Integer.Sparse.reindex key entry_5_3 = GramEntries.Block2.entries 5 3 := by
  decide +kernel

theorem entry_reindex_5_4 :
    Integer.Sparse.reindex key entry_5_4 = GramEntries.Block2.entries 5 4 := by
  decide +kernel

theorem entry_reindex_5_5 :
    Integer.Sparse.reindex key entry_5_5 = GramEntries.Block2.entries 5 5 := by
  decide +kernel

theorem entry_reindex_5_6 :
    Integer.Sparse.reindex key entry_5_6 = GramEntries.Block2.entries 5 6 := by
  decide +kernel

theorem entry_reindex_5_7 :
    Integer.Sparse.reindex key entry_5_7 = GramEntries.Block2.entries 5 7 := by
  decide +kernel

theorem entry_reindex_5_8 :
    Integer.Sparse.reindex key entry_5_8 = GramEntries.Block2.entries 5 8 := by
  decide +kernel

theorem entry_reindex_5_9 :
    Integer.Sparse.reindex key entry_5_9 = GramEntries.Block2.entries 5 9 := by
  decide +kernel

theorem entry_reindex_5_10 :
    Integer.Sparse.reindex key entry_5_10 = GramEntries.Block2.entries 5 10 := by
  decide +kernel

theorem entries_reindex_5 (j : Fin 11) :
    Integer.Sparse.reindex key (entries 5 j) = GramEntries.Block2.entries 5 j := by
  fin_cases j
  · exact entry_reindex_5_0
  · exact entry_reindex_5_1
  · exact entry_reindex_5_2
  · exact entry_reindex_5_3
  · exact entry_reindex_5_4
  · exact entry_reindex_5_5
  · exact entry_reindex_5_6
  · exact entry_reindex_5_7
  · exact entry_reindex_5_8
  · exact entry_reindex_5_9
  · exact entry_reindex_5_10

end MUB6.Certificate.GramAssembly.Block2

end OAI
