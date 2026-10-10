import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem entry_reindex_8_0 :
    Integer.Sparse.reindex key entry_8_0 = GramEntries.Block2.entries 8 0 := by
  decide +kernel

theorem entry_reindex_8_1 :
    Integer.Sparse.reindex key entry_8_1 = GramEntries.Block2.entries 8 1 := by
  decide +kernel

theorem entry_reindex_8_2 :
    Integer.Sparse.reindex key entry_8_2 = GramEntries.Block2.entries 8 2 := by
  decide +kernel

theorem entry_reindex_8_3 :
    Integer.Sparse.reindex key entry_8_3 = GramEntries.Block2.entries 8 3 := by
  decide +kernel

theorem entry_reindex_8_4 :
    Integer.Sparse.reindex key entry_8_4 = GramEntries.Block2.entries 8 4 := by
  decide +kernel

theorem entry_reindex_8_5 :
    Integer.Sparse.reindex key entry_8_5 = GramEntries.Block2.entries 8 5 := by
  decide +kernel

theorem entry_reindex_8_6 :
    Integer.Sparse.reindex key entry_8_6 = GramEntries.Block2.entries 8 6 := by
  decide +kernel

theorem entry_reindex_8_7 :
    Integer.Sparse.reindex key entry_8_7 = GramEntries.Block2.entries 8 7 := by
  decide +kernel

theorem entry_reindex_8_8 :
    Integer.Sparse.reindex key entry_8_8 = GramEntries.Block2.entries 8 8 := by
  decide +kernel

theorem entry_reindex_8_9 :
    Integer.Sparse.reindex key entry_8_9 = GramEntries.Block2.entries 8 9 := by
  decide +kernel

theorem entry_reindex_8_10 :
    Integer.Sparse.reindex key entry_8_10 = GramEntries.Block2.entries 8 10 := by
  decide +kernel

theorem entries_reindex_8 (j : Fin 11) :
    Integer.Sparse.reindex key (entries 8 j) = GramEntries.Block2.entries 8 j := by
  fin_cases j
  · exact entry_reindex_8_0
  · exact entry_reindex_8_1
  · exact entry_reindex_8_2
  · exact entry_reindex_8_3
  · exact entry_reindex_8_4
  · exact entry_reindex_8_5
  · exact entry_reindex_8_6
  · exact entry_reindex_8_7
  · exact entry_reindex_8_8
  · exact entry_reindex_8_9
  · exact entry_reindex_8_10

end MUB6.Certificate.GramAssembly.Block2

end OAI
