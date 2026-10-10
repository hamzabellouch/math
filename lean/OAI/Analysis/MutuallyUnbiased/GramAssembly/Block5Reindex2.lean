import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_2_0 :
    Integer.Sparse.reindex key entry_2_0 = GramEntries.Block5.entries 2 0 := by
  decide +kernel

theorem entry_reindex_2_1 :
    Integer.Sparse.reindex key entry_2_1 = GramEntries.Block5.entries 2 1 := by
  decide +kernel

theorem entry_reindex_2_2 :
    Integer.Sparse.reindex key entry_2_2 = GramEntries.Block5.entries 2 2 := by
  decide +kernel

theorem entry_reindex_2_3 :
    Integer.Sparse.reindex key entry_2_3 = GramEntries.Block5.entries 2 3 := by
  decide +kernel

theorem entry_reindex_2_4 :
    Integer.Sparse.reindex key entry_2_4 = GramEntries.Block5.entries 2 4 := by
  decide +kernel

theorem entry_reindex_2_5 :
    Integer.Sparse.reindex key entry_2_5 = GramEntries.Block5.entries 2 5 := by
  decide +kernel

theorem entry_reindex_2_6 :
    Integer.Sparse.reindex key entry_2_6 = GramEntries.Block5.entries 2 6 := by
  decide +kernel

theorem entry_reindex_2_7 :
    Integer.Sparse.reindex key entry_2_7 = GramEntries.Block5.entries 2 7 := by
  decide +kernel

theorem entry_reindex_2_8 :
    Integer.Sparse.reindex key entry_2_8 = GramEntries.Block5.entries 2 8 := by
  decide +kernel

theorem entry_reindex_2_9 :
    Integer.Sparse.reindex key entry_2_9 = GramEntries.Block5.entries 2 9 := by
  decide +kernel

theorem entry_reindex_2_10 :
    Integer.Sparse.reindex key entry_2_10 = GramEntries.Block5.entries 2 10 := by
  decide +kernel

theorem entry_reindex_2_11 :
    Integer.Sparse.reindex key entry_2_11 = GramEntries.Block5.entries 2 11 := by
  decide +kernel

theorem entries_reindex_2 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 2 j) = GramEntries.Block5.entries 2 j := by
  fin_cases j
  · exact entry_reindex_2_0
  · exact entry_reindex_2_1
  · exact entry_reindex_2_2
  · exact entry_reindex_2_3
  · exact entry_reindex_2_4
  · exact entry_reindex_2_5
  · exact entry_reindex_2_6
  · exact entry_reindex_2_7
  · exact entry_reindex_2_8
  · exact entry_reindex_2_9
  · exact entry_reindex_2_10
  · exact entry_reindex_2_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
