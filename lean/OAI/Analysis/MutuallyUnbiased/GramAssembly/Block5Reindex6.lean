import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_6_0 :
    Integer.Sparse.reindex key entry_6_0 = GramEntries.Block5.entries 6 0 := by
  decide +kernel

theorem entry_reindex_6_1 :
    Integer.Sparse.reindex key entry_6_1 = GramEntries.Block5.entries 6 1 := by
  decide +kernel

theorem entry_reindex_6_2 :
    Integer.Sparse.reindex key entry_6_2 = GramEntries.Block5.entries 6 2 := by
  decide +kernel

theorem entry_reindex_6_3 :
    Integer.Sparse.reindex key entry_6_3 = GramEntries.Block5.entries 6 3 := by
  decide +kernel

theorem entry_reindex_6_4 :
    Integer.Sparse.reindex key entry_6_4 = GramEntries.Block5.entries 6 4 := by
  decide +kernel

theorem entry_reindex_6_5 :
    Integer.Sparse.reindex key entry_6_5 = GramEntries.Block5.entries 6 5 := by
  decide +kernel

theorem entry_reindex_6_6 :
    Integer.Sparse.reindex key entry_6_6 = GramEntries.Block5.entries 6 6 := by
  decide +kernel

theorem entry_reindex_6_7 :
    Integer.Sparse.reindex key entry_6_7 = GramEntries.Block5.entries 6 7 := by
  decide +kernel

theorem entry_reindex_6_8 :
    Integer.Sparse.reindex key entry_6_8 = GramEntries.Block5.entries 6 8 := by
  decide +kernel

theorem entry_reindex_6_9 :
    Integer.Sparse.reindex key entry_6_9 = GramEntries.Block5.entries 6 9 := by
  decide +kernel

theorem entry_reindex_6_10 :
    Integer.Sparse.reindex key entry_6_10 = GramEntries.Block5.entries 6 10 := by
  decide +kernel

theorem entry_reindex_6_11 :
    Integer.Sparse.reindex key entry_6_11 = GramEntries.Block5.entries 6 11 := by
  decide +kernel

theorem entries_reindex_6 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 6 j) = GramEntries.Block5.entries 6 j := by
  fin_cases j
  · exact entry_reindex_6_0
  · exact entry_reindex_6_1
  · exact entry_reindex_6_2
  · exact entry_reindex_6_3
  · exact entry_reindex_6_4
  · exact entry_reindex_6_5
  · exact entry_reindex_6_6
  · exact entry_reindex_6_7
  · exact entry_reindex_6_8
  · exact entry_reindex_6_9
  · exact entry_reindex_6_10
  · exact entry_reindex_6_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
