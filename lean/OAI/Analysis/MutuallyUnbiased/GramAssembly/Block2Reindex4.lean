import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem entry_reindex_4_0 :
    Integer.Sparse.reindex key entry_4_0 = GramEntries.Block2.entries 4 0 := by
  decide +kernel

theorem entry_reindex_4_1 :
    Integer.Sparse.reindex key entry_4_1 = GramEntries.Block2.entries 4 1 := by
  decide +kernel

theorem entry_reindex_4_2 :
    Integer.Sparse.reindex key entry_4_2 = GramEntries.Block2.entries 4 2 := by
  decide +kernel

theorem entry_reindex_4_3 :
    Integer.Sparse.reindex key entry_4_3 = GramEntries.Block2.entries 4 3 := by
  decide +kernel

theorem entry_reindex_4_4 :
    Integer.Sparse.reindex key entry_4_4 = GramEntries.Block2.entries 4 4 := by
  decide +kernel

theorem entry_reindex_4_5 :
    Integer.Sparse.reindex key entry_4_5 = GramEntries.Block2.entries 4 5 := by
  decide +kernel

theorem entry_reindex_4_6 :
    Integer.Sparse.reindex key entry_4_6 = GramEntries.Block2.entries 4 6 := by
  decide +kernel

theorem entry_reindex_4_7 :
    Integer.Sparse.reindex key entry_4_7 = GramEntries.Block2.entries 4 7 := by
  decide +kernel

theorem entry_reindex_4_8 :
    Integer.Sparse.reindex key entry_4_8 = GramEntries.Block2.entries 4 8 := by
  decide +kernel

theorem entry_reindex_4_9 :
    Integer.Sparse.reindex key entry_4_9 = GramEntries.Block2.entries 4 9 := by
  decide +kernel

theorem entry_reindex_4_10 :
    Integer.Sparse.reindex key entry_4_10 = GramEntries.Block2.entries 4 10 := by
  decide +kernel

theorem entries_reindex_4 (j : Fin 11) :
    Integer.Sparse.reindex key (entries 4 j) = GramEntries.Block2.entries 4 j := by
  fin_cases j
  · exact entry_reindex_4_0
  · exact entry_reindex_4_1
  · exact entry_reindex_4_2
  · exact entry_reindex_4_3
  · exact entry_reindex_4_4
  · exact entry_reindex_4_5
  · exact entry_reindex_4_6
  · exact entry_reindex_4_7
  · exact entry_reindex_4_8
  · exact entry_reindex_4_9
  · exact entry_reindex_4_10

end MUB6.Certificate.GramAssembly.Block2

end OAI
