import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entry_reindex_5_0 :
    Integer.Sparse.reindex key entry_5_0 = GramEntries.Block4.entries 5 0 := by
  decide +kernel

theorem entry_reindex_5_1 :
    Integer.Sparse.reindex key entry_5_1 = GramEntries.Block4.entries 5 1 := by
  decide +kernel

theorem entry_reindex_5_2 :
    Integer.Sparse.reindex key entry_5_2 = GramEntries.Block4.entries 5 2 := by
  decide +kernel

theorem entry_reindex_5_3 :
    Integer.Sparse.reindex key entry_5_3 = GramEntries.Block4.entries 5 3 := by
  decide +kernel

theorem entry_reindex_5_4 :
    Integer.Sparse.reindex key entry_5_4 = GramEntries.Block4.entries 5 4 := by
  decide +kernel

theorem entry_reindex_5_5 :
    Integer.Sparse.reindex key entry_5_5 = GramEntries.Block4.entries 5 5 := by
  decide +kernel

theorem entry_reindex_5_6 :
    Integer.Sparse.reindex key entry_5_6 = GramEntries.Block4.entries 5 6 := by
  decide +kernel

theorem entry_reindex_5_7 :
    Integer.Sparse.reindex key entry_5_7 = GramEntries.Block4.entries 5 7 := by
  decide +kernel

theorem entry_reindex_5_8 :
    Integer.Sparse.reindex key entry_5_8 = GramEntries.Block4.entries 5 8 := by
  decide +kernel

theorem entry_reindex_5_9 :
    Integer.Sparse.reindex key entry_5_9 = GramEntries.Block4.entries 5 9 := by
  decide +kernel

theorem entry_reindex_5_10 :
    Integer.Sparse.reindex key entry_5_10 = GramEntries.Block4.entries 5 10 := by
  decide +kernel

theorem entry_reindex_5_11 :
    Integer.Sparse.reindex key entry_5_11 = GramEntries.Block4.entries 5 11 := by
  decide +kernel

theorem entry_reindex_5_12 :
    Integer.Sparse.reindex key entry_5_12 = GramEntries.Block4.entries 5 12 := by
  decide +kernel

theorem entry_reindex_5_13 :
    Integer.Sparse.reindex key entry_5_13 = GramEntries.Block4.entries 5 13 := by
  decide +kernel

theorem entry_reindex_5_14 :
    Integer.Sparse.reindex key entry_5_14 = GramEntries.Block4.entries 5 14 := by
  decide +kernel

theorem entry_reindex_5_15 :
    Integer.Sparse.reindex key entry_5_15 = GramEntries.Block4.entries 5 15 := by
  decide +kernel

theorem entry_reindex_5_16 :
    Integer.Sparse.reindex key entry_5_16 = GramEntries.Block4.entries 5 16 := by
  decide +kernel

theorem entry_reindex_5_17 :
    Integer.Sparse.reindex key entry_5_17 = GramEntries.Block4.entries 5 17 := by
  decide +kernel

theorem entry_reindex_5_18 :
    Integer.Sparse.reindex key entry_5_18 = GramEntries.Block4.entries 5 18 := by
  decide +kernel

theorem entry_reindex_5_19 :
    Integer.Sparse.reindex key entry_5_19 = GramEntries.Block4.entries 5 19 := by
  decide +kernel

theorem entry_reindex_5_20 :
    Integer.Sparse.reindex key entry_5_20 = GramEntries.Block4.entries 5 20 := by
  decide +kernel

theorem entry_reindex_5_21 :
    Integer.Sparse.reindex key entry_5_21 = GramEntries.Block4.entries 5 21 := by
  decide +kernel

theorem entries_reindex_5 (j : Fin 22) :
    Integer.Sparse.reindex key (entries 5 j) = GramEntries.Block4.entries 5 j := by
  fin_cases j
  · exact entry_reindex_5_0
  · exact entry_reindex_5_1
  · exact entry_reindex_5_2
  · exact entry_reindex_5_3
  · exact entry_reindex_5_4
  · exact entry_reindex_5_5
  · exact entry_reindex_5_6
  · exact entry_reindex_5_7
  · exact entry_reindex_5_8
  · exact entry_reindex_5_9
  · exact entry_reindex_5_10
  · exact entry_reindex_5_11
  · exact entry_reindex_5_12
  · exact entry_reindex_5_13
  · exact entry_reindex_5_14
  · exact entry_reindex_5_15
  · exact entry_reindex_5_16
  · exact entry_reindex_5_17
  · exact entry_reindex_5_18
  · exact entry_reindex_5_19
  · exact entry_reindex_5_20
  · exact entry_reindex_5_21

end MUB6.Certificate.GramAssembly.Block4

end OAI
