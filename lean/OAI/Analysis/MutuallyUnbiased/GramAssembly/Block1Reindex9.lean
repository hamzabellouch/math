import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_9_0 :
    Integer.Sparse.reindex key entry_9_0 = GramEntries.Block1.entries 9 0 := by
  decide +kernel

theorem entry_reindex_9_1 :
    Integer.Sparse.reindex key entry_9_1 = GramEntries.Block1.entries 9 1 := by
  decide +kernel

theorem entry_reindex_9_2 :
    Integer.Sparse.reindex key entry_9_2 = GramEntries.Block1.entries 9 2 := by
  decide +kernel

theorem entry_reindex_9_3 :
    Integer.Sparse.reindex key entry_9_3 = GramEntries.Block1.entries 9 3 := by
  decide +kernel

theorem entry_reindex_9_4 :
    Integer.Sparse.reindex key entry_9_4 = GramEntries.Block1.entries 9 4 := by
  decide +kernel

theorem entry_reindex_9_5 :
    Integer.Sparse.reindex key entry_9_5 = GramEntries.Block1.entries 9 5 := by
  decide +kernel

theorem entry_reindex_9_6 :
    Integer.Sparse.reindex key entry_9_6 = GramEntries.Block1.entries 9 6 := by
  decide +kernel

theorem entry_reindex_9_7 :
    Integer.Sparse.reindex key entry_9_7 = GramEntries.Block1.entries 9 7 := by
  decide +kernel

theorem entry_reindex_9_8 :
    Integer.Sparse.reindex key entry_9_8 = GramEntries.Block1.entries 9 8 := by
  decide +kernel

theorem entry_reindex_9_9 :
    Integer.Sparse.reindex key entry_9_9 = GramEntries.Block1.entries 9 9 := by
  decide +kernel

theorem entry_reindex_9_10 :
    Integer.Sparse.reindex key entry_9_10 = GramEntries.Block1.entries 9 10 := by
  decide +kernel

theorem entry_reindex_9_11 :
    Integer.Sparse.reindex key entry_9_11 = GramEntries.Block1.entries 9 11 := by
  decide +kernel

theorem entry_reindex_9_12 :
    Integer.Sparse.reindex key entry_9_12 = GramEntries.Block1.entries 9 12 := by
  decide +kernel

theorem entry_reindex_9_13 :
    Integer.Sparse.reindex key entry_9_13 = GramEntries.Block1.entries 9 13 := by
  decide +kernel

theorem entry_reindex_9_14 :
    Integer.Sparse.reindex key entry_9_14 = GramEntries.Block1.entries 9 14 := by
  decide +kernel

theorem entry_reindex_9_15 :
    Integer.Sparse.reindex key entry_9_15 = GramEntries.Block1.entries 9 15 := by
  decide +kernel

theorem entry_reindex_9_16 :
    Integer.Sparse.reindex key entry_9_16 = GramEntries.Block1.entries 9 16 := by
  decide +kernel

theorem entry_reindex_9_17 :
    Integer.Sparse.reindex key entry_9_17 = GramEntries.Block1.entries 9 17 := by
  decide +kernel

theorem entry_reindex_9_18 :
    Integer.Sparse.reindex key entry_9_18 = GramEntries.Block1.entries 9 18 := by
  decide +kernel

theorem entry_reindex_9_19 :
    Integer.Sparse.reindex key entry_9_19 = GramEntries.Block1.entries 9 19 := by
  decide +kernel

theorem entry_reindex_9_20 :
    Integer.Sparse.reindex key entry_9_20 = GramEntries.Block1.entries 9 20 := by
  decide +kernel

theorem entries_reindex_9 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 9 j) = GramEntries.Block1.entries 9 j := by
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
  · exact entry_reindex_9_11
  · exact entry_reindex_9_12
  · exact entry_reindex_9_13
  · exact entry_reindex_9_14
  · exact entry_reindex_9_15
  · exact entry_reindex_9_16
  · exact entry_reindex_9_17
  · exact entry_reindex_9_18
  · exact entry_reindex_9_19
  · exact entry_reindex_9_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
