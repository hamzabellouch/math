import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entry_reindex_7_0 :
    Integer.Sparse.reindex key entry_7_0 = GramEntries.Block4.entries 7 0 := by
  decide +kernel

theorem entry_reindex_7_1 :
    Integer.Sparse.reindex key entry_7_1 = GramEntries.Block4.entries 7 1 := by
  decide +kernel

theorem entry_reindex_7_2 :
    Integer.Sparse.reindex key entry_7_2 = GramEntries.Block4.entries 7 2 := by
  decide +kernel

theorem entry_reindex_7_3 :
    Integer.Sparse.reindex key entry_7_3 = GramEntries.Block4.entries 7 3 := by
  decide +kernel

theorem entry_reindex_7_4 :
    Integer.Sparse.reindex key entry_7_4 = GramEntries.Block4.entries 7 4 := by
  decide +kernel

theorem entry_reindex_7_5 :
    Integer.Sparse.reindex key entry_7_5 = GramEntries.Block4.entries 7 5 := by
  decide +kernel

theorem entry_reindex_7_6 :
    Integer.Sparse.reindex key entry_7_6 = GramEntries.Block4.entries 7 6 := by
  decide +kernel

theorem entry_reindex_7_7 :
    Integer.Sparse.reindex key entry_7_7 = GramEntries.Block4.entries 7 7 := by
  decide +kernel

theorem entry_reindex_7_8 :
    Integer.Sparse.reindex key entry_7_8 = GramEntries.Block4.entries 7 8 := by
  decide +kernel

theorem entry_reindex_7_9 :
    Integer.Sparse.reindex key entry_7_9 = GramEntries.Block4.entries 7 9 := by
  decide +kernel

theorem entry_reindex_7_10 :
    Integer.Sparse.reindex key entry_7_10 = GramEntries.Block4.entries 7 10 := by
  decide +kernel

theorem entry_reindex_7_11 :
    Integer.Sparse.reindex key entry_7_11 = GramEntries.Block4.entries 7 11 := by
  decide +kernel

theorem entry_reindex_7_12 :
    Integer.Sparse.reindex key entry_7_12 = GramEntries.Block4.entries 7 12 := by
  decide +kernel

theorem entry_reindex_7_13 :
    Integer.Sparse.reindex key entry_7_13 = GramEntries.Block4.entries 7 13 := by
  decide +kernel

theorem entry_reindex_7_14 :
    Integer.Sparse.reindex key entry_7_14 = GramEntries.Block4.entries 7 14 := by
  decide +kernel

theorem entry_reindex_7_15 :
    Integer.Sparse.reindex key entry_7_15 = GramEntries.Block4.entries 7 15 := by
  decide +kernel

theorem entry_reindex_7_16 :
    Integer.Sparse.reindex key entry_7_16 = GramEntries.Block4.entries 7 16 := by
  decide +kernel

theorem entry_reindex_7_17 :
    Integer.Sparse.reindex key entry_7_17 = GramEntries.Block4.entries 7 17 := by
  decide +kernel

theorem entry_reindex_7_18 :
    Integer.Sparse.reindex key entry_7_18 = GramEntries.Block4.entries 7 18 := by
  decide +kernel

theorem entry_reindex_7_19 :
    Integer.Sparse.reindex key entry_7_19 = GramEntries.Block4.entries 7 19 := by
  decide +kernel

theorem entry_reindex_7_20 :
    Integer.Sparse.reindex key entry_7_20 = GramEntries.Block4.entries 7 20 := by
  decide +kernel

theorem entry_reindex_7_21 :
    Integer.Sparse.reindex key entry_7_21 = GramEntries.Block4.entries 7 21 := by
  decide +kernel

theorem entries_reindex_7 (j : Fin 22) :
    Integer.Sparse.reindex key (entries 7 j) = GramEntries.Block4.entries 7 j := by
  fin_cases j
  · exact entry_reindex_7_0
  · exact entry_reindex_7_1
  · exact entry_reindex_7_2
  · exact entry_reindex_7_3
  · exact entry_reindex_7_4
  · exact entry_reindex_7_5
  · exact entry_reindex_7_6
  · exact entry_reindex_7_7
  · exact entry_reindex_7_8
  · exact entry_reindex_7_9
  · exact entry_reindex_7_10
  · exact entry_reindex_7_11
  · exact entry_reindex_7_12
  · exact entry_reindex_7_13
  · exact entry_reindex_7_14
  · exact entry_reindex_7_15
  · exact entry_reindex_7_16
  · exact entry_reindex_7_17
  · exact entry_reindex_7_18
  · exact entry_reindex_7_19
  · exact entry_reindex_7_20
  · exact entry_reindex_7_21

end MUB6.Certificate.GramAssembly.Block4

end OAI
