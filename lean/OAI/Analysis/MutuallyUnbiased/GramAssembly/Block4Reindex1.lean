import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entry_reindex_1_0 :
    Integer.Sparse.reindex key entry_1_0 = GramEntries.Block4.entries 1 0 := by
  decide +kernel

theorem entry_reindex_1_1 :
    Integer.Sparse.reindex key entry_1_1 = GramEntries.Block4.entries 1 1 := by
  decide +kernel

theorem entry_reindex_1_2 :
    Integer.Sparse.reindex key entry_1_2 = GramEntries.Block4.entries 1 2 := by
  decide +kernel

theorem entry_reindex_1_3 :
    Integer.Sparse.reindex key entry_1_3 = GramEntries.Block4.entries 1 3 := by
  decide +kernel

theorem entry_reindex_1_4 :
    Integer.Sparse.reindex key entry_1_4 = GramEntries.Block4.entries 1 4 := by
  decide +kernel

theorem entry_reindex_1_5 :
    Integer.Sparse.reindex key entry_1_5 = GramEntries.Block4.entries 1 5 := by
  decide +kernel

theorem entry_reindex_1_6 :
    Integer.Sparse.reindex key entry_1_6 = GramEntries.Block4.entries 1 6 := by
  decide +kernel

theorem entry_reindex_1_7 :
    Integer.Sparse.reindex key entry_1_7 = GramEntries.Block4.entries 1 7 := by
  decide +kernel

theorem entry_reindex_1_8 :
    Integer.Sparse.reindex key entry_1_8 = GramEntries.Block4.entries 1 8 := by
  decide +kernel

theorem entry_reindex_1_9 :
    Integer.Sparse.reindex key entry_1_9 = GramEntries.Block4.entries 1 9 := by
  decide +kernel

theorem entry_reindex_1_10 :
    Integer.Sparse.reindex key entry_1_10 = GramEntries.Block4.entries 1 10 := by
  decide +kernel

theorem entry_reindex_1_11 :
    Integer.Sparse.reindex key entry_1_11 = GramEntries.Block4.entries 1 11 := by
  decide +kernel

theorem entry_reindex_1_12 :
    Integer.Sparse.reindex key entry_1_12 = GramEntries.Block4.entries 1 12 := by
  decide +kernel

theorem entry_reindex_1_13 :
    Integer.Sparse.reindex key entry_1_13 = GramEntries.Block4.entries 1 13 := by
  decide +kernel

theorem entry_reindex_1_14 :
    Integer.Sparse.reindex key entry_1_14 = GramEntries.Block4.entries 1 14 := by
  decide +kernel

theorem entry_reindex_1_15 :
    Integer.Sparse.reindex key entry_1_15 = GramEntries.Block4.entries 1 15 := by
  decide +kernel

theorem entry_reindex_1_16 :
    Integer.Sparse.reindex key entry_1_16 = GramEntries.Block4.entries 1 16 := by
  decide +kernel

theorem entry_reindex_1_17 :
    Integer.Sparse.reindex key entry_1_17 = GramEntries.Block4.entries 1 17 := by
  decide +kernel

theorem entry_reindex_1_18 :
    Integer.Sparse.reindex key entry_1_18 = GramEntries.Block4.entries 1 18 := by
  decide +kernel

theorem entry_reindex_1_19 :
    Integer.Sparse.reindex key entry_1_19 = GramEntries.Block4.entries 1 19 := by
  decide +kernel

theorem entry_reindex_1_20 :
    Integer.Sparse.reindex key entry_1_20 = GramEntries.Block4.entries 1 20 := by
  decide +kernel

theorem entry_reindex_1_21 :
    Integer.Sparse.reindex key entry_1_21 = GramEntries.Block4.entries 1 21 := by
  decide +kernel

theorem entries_reindex_1 (j : Fin 22) :
    Integer.Sparse.reindex key (entries 1 j) = GramEntries.Block4.entries 1 j := by
  fin_cases j
  · exact entry_reindex_1_0
  · exact entry_reindex_1_1
  · exact entry_reindex_1_2
  · exact entry_reindex_1_3
  · exact entry_reindex_1_4
  · exact entry_reindex_1_5
  · exact entry_reindex_1_6
  · exact entry_reindex_1_7
  · exact entry_reindex_1_8
  · exact entry_reindex_1_9
  · exact entry_reindex_1_10
  · exact entry_reindex_1_11
  · exact entry_reindex_1_12
  · exact entry_reindex_1_13
  · exact entry_reindex_1_14
  · exact entry_reindex_1_15
  · exact entry_reindex_1_16
  · exact entry_reindex_1_17
  · exact entry_reindex_1_18
  · exact entry_reindex_1_19
  · exact entry_reindex_1_20
  · exact entry_reindex_1_21

end MUB6.Certificate.GramAssembly.Block4

end OAI
