import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entry_reindex_11_0 :
    Integer.Sparse.reindex key entry_11_0 = GramEntries.Block4.entries 11 0 := by
  decide +kernel

theorem entry_reindex_11_1 :
    Integer.Sparse.reindex key entry_11_1 = GramEntries.Block4.entries 11 1 := by
  decide +kernel

theorem entry_reindex_11_2 :
    Integer.Sparse.reindex key entry_11_2 = GramEntries.Block4.entries 11 2 := by
  decide +kernel

theorem entry_reindex_11_3 :
    Integer.Sparse.reindex key entry_11_3 = GramEntries.Block4.entries 11 3 := by
  decide +kernel

theorem entry_reindex_11_4 :
    Integer.Sparse.reindex key entry_11_4 = GramEntries.Block4.entries 11 4 := by
  decide +kernel

theorem entry_reindex_11_5 :
    Integer.Sparse.reindex key entry_11_5 = GramEntries.Block4.entries 11 5 := by
  decide +kernel

theorem entry_reindex_11_6 :
    Integer.Sparse.reindex key entry_11_6 = GramEntries.Block4.entries 11 6 := by
  decide +kernel

theorem entry_reindex_11_7 :
    Integer.Sparse.reindex key entry_11_7 = GramEntries.Block4.entries 11 7 := by
  decide +kernel

theorem entry_reindex_11_8 :
    Integer.Sparse.reindex key entry_11_8 = GramEntries.Block4.entries 11 8 := by
  decide +kernel

theorem entry_reindex_11_9 :
    Integer.Sparse.reindex key entry_11_9 = GramEntries.Block4.entries 11 9 := by
  decide +kernel

theorem entry_reindex_11_10 :
    Integer.Sparse.reindex key entry_11_10 = GramEntries.Block4.entries 11 10 := by
  decide +kernel

theorem entry_reindex_11_11 :
    Integer.Sparse.reindex key entry_11_11 = GramEntries.Block4.entries 11 11 := by
  decide +kernel

theorem entry_reindex_11_12 :
    Integer.Sparse.reindex key entry_11_12 = GramEntries.Block4.entries 11 12 := by
  decide +kernel

theorem entry_reindex_11_13 :
    Integer.Sparse.reindex key entry_11_13 = GramEntries.Block4.entries 11 13 := by
  decide +kernel

theorem entry_reindex_11_14 :
    Integer.Sparse.reindex key entry_11_14 = GramEntries.Block4.entries 11 14 := by
  decide +kernel

theorem entry_reindex_11_15 :
    Integer.Sparse.reindex key entry_11_15 = GramEntries.Block4.entries 11 15 := by
  decide +kernel

theorem entry_reindex_11_16 :
    Integer.Sparse.reindex key entry_11_16 = GramEntries.Block4.entries 11 16 := by
  decide +kernel

theorem entry_reindex_11_17 :
    Integer.Sparse.reindex key entry_11_17 = GramEntries.Block4.entries 11 17 := by
  decide +kernel

theorem entry_reindex_11_18 :
    Integer.Sparse.reindex key entry_11_18 = GramEntries.Block4.entries 11 18 := by
  decide +kernel

theorem entry_reindex_11_19 :
    Integer.Sparse.reindex key entry_11_19 = GramEntries.Block4.entries 11 19 := by
  decide +kernel

theorem entry_reindex_11_20 :
    Integer.Sparse.reindex key entry_11_20 = GramEntries.Block4.entries 11 20 := by
  decide +kernel

theorem entry_reindex_11_21 :
    Integer.Sparse.reindex key entry_11_21 = GramEntries.Block4.entries 11 21 := by
  decide +kernel

theorem entries_reindex_11 (j : Fin 22) :
    Integer.Sparse.reindex key (entries 11 j) = GramEntries.Block4.entries 11 j := by
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
  · exact entry_reindex_11_12
  · exact entry_reindex_11_13
  · exact entry_reindex_11_14
  · exact entry_reindex_11_15
  · exact entry_reindex_11_16
  · exact entry_reindex_11_17
  · exact entry_reindex_11_18
  · exact entry_reindex_11_19
  · exact entry_reindex_11_20
  · exact entry_reindex_11_21

end MUB6.Certificate.GramAssembly.Block4

end OAI
