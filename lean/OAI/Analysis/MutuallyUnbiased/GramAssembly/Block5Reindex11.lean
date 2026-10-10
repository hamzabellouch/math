import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_11_0 :
    Integer.Sparse.reindex key entry_11_0 = GramEntries.Block5.entries 11 0 := by
  decide +kernel

theorem entry_reindex_11_1 :
    Integer.Sparse.reindex key entry_11_1 = GramEntries.Block5.entries 11 1 := by
  decide +kernel

theorem entry_reindex_11_2 :
    Integer.Sparse.reindex key entry_11_2 = GramEntries.Block5.entries 11 2 := by
  decide +kernel

theorem entry_reindex_11_3 :
    Integer.Sparse.reindex key entry_11_3 = GramEntries.Block5.entries 11 3 := by
  decide +kernel

theorem entry_reindex_11_4 :
    Integer.Sparse.reindex key entry_11_4 = GramEntries.Block5.entries 11 4 := by
  decide +kernel

theorem entry_reindex_11_5 :
    Integer.Sparse.reindex key entry_11_5 = GramEntries.Block5.entries 11 5 := by
  decide +kernel

theorem entry_reindex_11_6 :
    Integer.Sparse.reindex key entry_11_6 = GramEntries.Block5.entries 11 6 := by
  decide +kernel

theorem entry_reindex_11_7 :
    Integer.Sparse.reindex key entry_11_7 = GramEntries.Block5.entries 11 7 := by
  decide +kernel

theorem entry_reindex_11_8 :
    Integer.Sparse.reindex key entry_11_8 = GramEntries.Block5.entries 11 8 := by
  decide +kernel

theorem entry_reindex_11_9 :
    Integer.Sparse.reindex key entry_11_9 = GramEntries.Block5.entries 11 9 := by
  decide +kernel

theorem entry_reindex_11_10 :
    Integer.Sparse.reindex key entry_11_10 = GramEntries.Block5.entries 11 10 := by
  decide +kernel

theorem entry_reindex_11_11 :
    Integer.Sparse.reindex key entry_11_11 = GramEntries.Block5.entries 11 11 := by
  decide +kernel

theorem entries_reindex_11 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 11 j) = GramEntries.Block5.entries 11 j := by
  fin_cases j
  · exact entry_reindex_11_0
  · exact entry_reindex_11_1
  · exact entry_reindex_11_2
  · exact entry_reindex_11_3
  · exact entry_reindex_11_4
  · exact entry_reindex_11_5
  · exact entry_reindex_11_6
  · exact entry_reindex_11_7
  · exact entry_reindex_11_8
  · exact entry_reindex_11_9
  · exact entry_reindex_11_10
  · exact entry_reindex_11_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
