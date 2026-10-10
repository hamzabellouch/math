import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_10_0 :
    Integer.Sparse.reindex key entry_10_0 = GramEntries.Block1.entries 10 0 := by
  decide +kernel

theorem entry_reindex_10_1 :
    Integer.Sparse.reindex key entry_10_1 = GramEntries.Block1.entries 10 1 := by
  decide +kernel

theorem entry_reindex_10_2 :
    Integer.Sparse.reindex key entry_10_2 = GramEntries.Block1.entries 10 2 := by
  decide +kernel

theorem entry_reindex_10_3 :
    Integer.Sparse.reindex key entry_10_3 = GramEntries.Block1.entries 10 3 := by
  decide +kernel

theorem entry_reindex_10_4 :
    Integer.Sparse.reindex key entry_10_4 = GramEntries.Block1.entries 10 4 := by
  decide +kernel

theorem entry_reindex_10_5 :
    Integer.Sparse.reindex key entry_10_5 = GramEntries.Block1.entries 10 5 := by
  decide +kernel

theorem entry_reindex_10_6 :
    Integer.Sparse.reindex key entry_10_6 = GramEntries.Block1.entries 10 6 := by
  decide +kernel

theorem entry_reindex_10_7 :
    Integer.Sparse.reindex key entry_10_7 = GramEntries.Block1.entries 10 7 := by
  decide +kernel

theorem entry_reindex_10_8 :
    Integer.Sparse.reindex key entry_10_8 = GramEntries.Block1.entries 10 8 := by
  decide +kernel

theorem entry_reindex_10_9 :
    Integer.Sparse.reindex key entry_10_9 = GramEntries.Block1.entries 10 9 := by
  decide +kernel

theorem entry_reindex_10_10 :
    Integer.Sparse.reindex key entry_10_10 = GramEntries.Block1.entries 10 10 := by
  decide +kernel

theorem entry_reindex_10_11 :
    Integer.Sparse.reindex key entry_10_11 = GramEntries.Block1.entries 10 11 := by
  decide +kernel

theorem entry_reindex_10_12 :
    Integer.Sparse.reindex key entry_10_12 = GramEntries.Block1.entries 10 12 := by
  decide +kernel

theorem entry_reindex_10_13 :
    Integer.Sparse.reindex key entry_10_13 = GramEntries.Block1.entries 10 13 := by
  decide +kernel

theorem entry_reindex_10_14 :
    Integer.Sparse.reindex key entry_10_14 = GramEntries.Block1.entries 10 14 := by
  decide +kernel

theorem entry_reindex_10_15 :
    Integer.Sparse.reindex key entry_10_15 = GramEntries.Block1.entries 10 15 := by
  decide +kernel

theorem entry_reindex_10_16 :
    Integer.Sparse.reindex key entry_10_16 = GramEntries.Block1.entries 10 16 := by
  decide +kernel

theorem entry_reindex_10_17 :
    Integer.Sparse.reindex key entry_10_17 = GramEntries.Block1.entries 10 17 := by
  decide +kernel

theorem entry_reindex_10_18 :
    Integer.Sparse.reindex key entry_10_18 = GramEntries.Block1.entries 10 18 := by
  decide +kernel

theorem entry_reindex_10_19 :
    Integer.Sparse.reindex key entry_10_19 = GramEntries.Block1.entries 10 19 := by
  decide +kernel

theorem entry_reindex_10_20 :
    Integer.Sparse.reindex key entry_10_20 = GramEntries.Block1.entries 10 20 := by
  decide +kernel

theorem entries_reindex_10 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 10 j) = GramEntries.Block1.entries 10 j := by
  fin_cases j
  · exact entry_reindex_10_0
  · exact entry_reindex_10_1
  · exact entry_reindex_10_2
  · exact entry_reindex_10_3
  · exact entry_reindex_10_4
  · exact entry_reindex_10_5
  · exact entry_reindex_10_6
  · exact entry_reindex_10_7
  · exact entry_reindex_10_8
  · exact entry_reindex_10_9
  · exact entry_reindex_10_10
  · exact entry_reindex_10_11
  · exact entry_reindex_10_12
  · exact entry_reindex_10_13
  · exact entry_reindex_10_14
  · exact entry_reindex_10_15
  · exact entry_reindex_10_16
  · exact entry_reindex_10_17
  · exact entry_reindex_10_18
  · exact entry_reindex_10_19
  · exact entry_reindex_10_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
