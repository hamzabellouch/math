import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entry_reindex_0_0 :
    Integer.Sparse.reindex key entry_0_0 = GramEntries.Block4.entries 0 0 := by
  decide +kernel

theorem entry_reindex_0_1 :
    Integer.Sparse.reindex key entry_0_1 = GramEntries.Block4.entries 0 1 := by
  decide +kernel

theorem entry_reindex_0_2 :
    Integer.Sparse.reindex key entry_0_2 = GramEntries.Block4.entries 0 2 := by
  decide +kernel

theorem entry_reindex_0_3 :
    Integer.Sparse.reindex key entry_0_3 = GramEntries.Block4.entries 0 3 := by
  decide +kernel

theorem entry_reindex_0_4 :
    Integer.Sparse.reindex key entry_0_4 = GramEntries.Block4.entries 0 4 := by
  decide +kernel

theorem entry_reindex_0_5 :
    Integer.Sparse.reindex key entry_0_5 = GramEntries.Block4.entries 0 5 := by
  decide +kernel

theorem entry_reindex_0_6 :
    Integer.Sparse.reindex key entry_0_6 = GramEntries.Block4.entries 0 6 := by
  decide +kernel

theorem entry_reindex_0_7 :
    Integer.Sparse.reindex key entry_0_7 = GramEntries.Block4.entries 0 7 := by
  decide +kernel

theorem entry_reindex_0_8 :
    Integer.Sparse.reindex key entry_0_8 = GramEntries.Block4.entries 0 8 := by
  decide +kernel

theorem entry_reindex_0_9 :
    Integer.Sparse.reindex key entry_0_9 = GramEntries.Block4.entries 0 9 := by
  decide +kernel

theorem entry_reindex_0_10 :
    Integer.Sparse.reindex key entry_0_10 = GramEntries.Block4.entries 0 10 := by
  decide +kernel

theorem entry_reindex_0_11 :
    Integer.Sparse.reindex key entry_0_11 = GramEntries.Block4.entries 0 11 := by
  decide +kernel

theorem entry_reindex_0_12 :
    Integer.Sparse.reindex key entry_0_12 = GramEntries.Block4.entries 0 12 := by
  decide +kernel

theorem entry_reindex_0_13 :
    Integer.Sparse.reindex key entry_0_13 = GramEntries.Block4.entries 0 13 := by
  decide +kernel

theorem entry_reindex_0_14 :
    Integer.Sparse.reindex key entry_0_14 = GramEntries.Block4.entries 0 14 := by
  decide +kernel

theorem entry_reindex_0_15 :
    Integer.Sparse.reindex key entry_0_15 = GramEntries.Block4.entries 0 15 := by
  decide +kernel

theorem entry_reindex_0_16 :
    Integer.Sparse.reindex key entry_0_16 = GramEntries.Block4.entries 0 16 := by
  decide +kernel

theorem entry_reindex_0_17 :
    Integer.Sparse.reindex key entry_0_17 = GramEntries.Block4.entries 0 17 := by
  decide +kernel

theorem entry_reindex_0_18 :
    Integer.Sparse.reindex key entry_0_18 = GramEntries.Block4.entries 0 18 := by
  decide +kernel

theorem entry_reindex_0_19 :
    Integer.Sparse.reindex key entry_0_19 = GramEntries.Block4.entries 0 19 := by
  decide +kernel

theorem entry_reindex_0_20 :
    Integer.Sparse.reindex key entry_0_20 = GramEntries.Block4.entries 0 20 := by
  decide +kernel

theorem entry_reindex_0_21 :
    Integer.Sparse.reindex key entry_0_21 = GramEntries.Block4.entries 0 21 := by
  decide +kernel

theorem entries_reindex_0 (j : Fin 22) :
    Integer.Sparse.reindex key (entries 0 j) = GramEntries.Block4.entries 0 j := by
  fin_cases j
  · exact entry_reindex_0_0
  · exact entry_reindex_0_1
  · exact entry_reindex_0_2
  · exact entry_reindex_0_3
  · exact entry_reindex_0_4
  · exact entry_reindex_0_5
  · exact entry_reindex_0_6
  · exact entry_reindex_0_7
  · exact entry_reindex_0_8
  · exact entry_reindex_0_9
  · exact entry_reindex_0_10
  · exact entry_reindex_0_11
  · exact entry_reindex_0_12
  · exact entry_reindex_0_13
  · exact entry_reindex_0_14
  · exact entry_reindex_0_15
  · exact entry_reindex_0_16
  · exact entry_reindex_0_17
  · exact entry_reindex_0_18
  · exact entry_reindex_0_19
  · exact entry_reindex_0_20
  · exact entry_reindex_0_21

end MUB6.Certificate.GramAssembly.Block4

end OAI
