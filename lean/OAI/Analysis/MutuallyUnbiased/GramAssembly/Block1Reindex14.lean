import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_14_0 :
    Integer.Sparse.reindex key entry_14_0 = GramEntries.Block1.entries 14 0 := by
  decide +kernel

theorem entry_reindex_14_1 :
    Integer.Sparse.reindex key entry_14_1 = GramEntries.Block1.entries 14 1 := by
  decide +kernel

theorem entry_reindex_14_2 :
    Integer.Sparse.reindex key entry_14_2 = GramEntries.Block1.entries 14 2 := by
  decide +kernel

theorem entry_reindex_14_3 :
    Integer.Sparse.reindex key entry_14_3 = GramEntries.Block1.entries 14 3 := by
  decide +kernel

theorem entry_reindex_14_4 :
    Integer.Sparse.reindex key entry_14_4 = GramEntries.Block1.entries 14 4 := by
  decide +kernel

theorem entry_reindex_14_5 :
    Integer.Sparse.reindex key entry_14_5 = GramEntries.Block1.entries 14 5 := by
  decide +kernel

theorem entry_reindex_14_6 :
    Integer.Sparse.reindex key entry_14_6 = GramEntries.Block1.entries 14 6 := by
  decide +kernel

theorem entry_reindex_14_7 :
    Integer.Sparse.reindex key entry_14_7 = GramEntries.Block1.entries 14 7 := by
  decide +kernel

theorem entry_reindex_14_8 :
    Integer.Sparse.reindex key entry_14_8 = GramEntries.Block1.entries 14 8 := by
  decide +kernel

theorem entry_reindex_14_9 :
    Integer.Sparse.reindex key entry_14_9 = GramEntries.Block1.entries 14 9 := by
  decide +kernel

theorem entry_reindex_14_10 :
    Integer.Sparse.reindex key entry_14_10 = GramEntries.Block1.entries 14 10 := by
  decide +kernel

theorem entry_reindex_14_11 :
    Integer.Sparse.reindex key entry_14_11 = GramEntries.Block1.entries 14 11 := by
  decide +kernel

theorem entry_reindex_14_12 :
    Integer.Sparse.reindex key entry_14_12 = GramEntries.Block1.entries 14 12 := by
  decide +kernel

theorem entry_reindex_14_13 :
    Integer.Sparse.reindex key entry_14_13 = GramEntries.Block1.entries 14 13 := by
  decide +kernel

theorem entry_reindex_14_14 :
    Integer.Sparse.reindex key entry_14_14 = GramEntries.Block1.entries 14 14 := by
  decide +kernel

theorem entry_reindex_14_15 :
    Integer.Sparse.reindex key entry_14_15 = GramEntries.Block1.entries 14 15 := by
  decide +kernel

theorem entry_reindex_14_16 :
    Integer.Sparse.reindex key entry_14_16 = GramEntries.Block1.entries 14 16 := by
  decide +kernel

theorem entry_reindex_14_17 :
    Integer.Sparse.reindex key entry_14_17 = GramEntries.Block1.entries 14 17 := by
  decide +kernel

theorem entry_reindex_14_18 :
    Integer.Sparse.reindex key entry_14_18 = GramEntries.Block1.entries 14 18 := by
  decide +kernel

theorem entry_reindex_14_19 :
    Integer.Sparse.reindex key entry_14_19 = GramEntries.Block1.entries 14 19 := by
  decide +kernel

theorem entry_reindex_14_20 :
    Integer.Sparse.reindex key entry_14_20 = GramEntries.Block1.entries 14 20 := by
  decide +kernel

theorem entries_reindex_14 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 14 j) = GramEntries.Block1.entries 14 j := by
  fin_cases j
  · exact entry_reindex_14_0
  · exact entry_reindex_14_1
  · exact entry_reindex_14_2
  · exact entry_reindex_14_3
  · exact entry_reindex_14_4
  · exact entry_reindex_14_5
  · exact entry_reindex_14_6
  · exact entry_reindex_14_7
  · exact entry_reindex_14_8
  · exact entry_reindex_14_9
  · exact entry_reindex_14_10
  · exact entry_reindex_14_11
  · exact entry_reindex_14_12
  · exact entry_reindex_14_13
  · exact entry_reindex_14_14
  · exact entry_reindex_14_15
  · exact entry_reindex_14_16
  · exact entry_reindex_14_17
  · exact entry_reindex_14_18
  · exact entry_reindex_14_19
  · exact entry_reindex_14_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
