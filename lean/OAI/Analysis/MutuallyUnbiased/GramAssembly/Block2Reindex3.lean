import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem entry_reindex_3_0 :
    Integer.Sparse.reindex key entry_3_0 = GramEntries.Block2.entries 3 0 := by
  decide +kernel

theorem entry_reindex_3_1 :
    Integer.Sparse.reindex key entry_3_1 = GramEntries.Block2.entries 3 1 := by
  decide +kernel

theorem entry_reindex_3_2 :
    Integer.Sparse.reindex key entry_3_2 = GramEntries.Block2.entries 3 2 := by
  decide +kernel

theorem entry_reindex_3_3 :
    Integer.Sparse.reindex key entry_3_3 = GramEntries.Block2.entries 3 3 := by
  decide +kernel

theorem entry_reindex_3_4 :
    Integer.Sparse.reindex key entry_3_4 = GramEntries.Block2.entries 3 4 := by
  decide +kernel

theorem entry_reindex_3_5 :
    Integer.Sparse.reindex key entry_3_5 = GramEntries.Block2.entries 3 5 := by
  decide +kernel

theorem entry_reindex_3_6 :
    Integer.Sparse.reindex key entry_3_6 = GramEntries.Block2.entries 3 6 := by
  decide +kernel

theorem entry_reindex_3_7 :
    Integer.Sparse.reindex key entry_3_7 = GramEntries.Block2.entries 3 7 := by
  decide +kernel

theorem entry_reindex_3_8 :
    Integer.Sparse.reindex key entry_3_8 = GramEntries.Block2.entries 3 8 := by
  decide +kernel

theorem entry_reindex_3_9 :
    Integer.Sparse.reindex key entry_3_9 = GramEntries.Block2.entries 3 9 := by
  decide +kernel

theorem entry_reindex_3_10 :
    Integer.Sparse.reindex key entry_3_10 = GramEntries.Block2.entries 3 10 := by
  decide +kernel

theorem entries_reindex_3 (j : Fin 11) :
    Integer.Sparse.reindex key (entries 3 j) = GramEntries.Block2.entries 3 j := by
  fin_cases j
  · exact entry_reindex_3_0
  · exact entry_reindex_3_1
  · exact entry_reindex_3_2
  · exact entry_reindex_3_3
  · exact entry_reindex_3_4
  · exact entry_reindex_3_5
  · exact entry_reindex_3_6
  · exact entry_reindex_3_7
  · exact entry_reindex_3_8
  · exact entry_reindex_3_9
  · exact entry_reindex_3_10

end MUB6.Certificate.GramAssembly.Block2

end OAI
