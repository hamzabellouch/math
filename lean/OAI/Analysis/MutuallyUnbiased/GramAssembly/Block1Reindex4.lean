import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_4_0 :
    Integer.Sparse.reindex key entry_4_0 = GramEntries.Block1.entries 4 0 := by
  decide +kernel

theorem entry_reindex_4_1 :
    Integer.Sparse.reindex key entry_4_1 = GramEntries.Block1.entries 4 1 := by
  decide +kernel

theorem entry_reindex_4_2 :
    Integer.Sparse.reindex key entry_4_2 = GramEntries.Block1.entries 4 2 := by
  decide +kernel

theorem entry_reindex_4_3 :
    Integer.Sparse.reindex key entry_4_3 = GramEntries.Block1.entries 4 3 := by
  decide +kernel

theorem entry_reindex_4_4 :
    Integer.Sparse.reindex key entry_4_4 = GramEntries.Block1.entries 4 4 := by
  decide +kernel

theorem entry_reindex_4_5 :
    Integer.Sparse.reindex key entry_4_5 = GramEntries.Block1.entries 4 5 := by
  decide +kernel

theorem entry_reindex_4_6 :
    Integer.Sparse.reindex key entry_4_6 = GramEntries.Block1.entries 4 6 := by
  decide +kernel

theorem entry_reindex_4_7 :
    Integer.Sparse.reindex key entry_4_7 = GramEntries.Block1.entries 4 7 := by
  decide +kernel

theorem entry_reindex_4_8 :
    Integer.Sparse.reindex key entry_4_8 = GramEntries.Block1.entries 4 8 := by
  decide +kernel

theorem entry_reindex_4_9 :
    Integer.Sparse.reindex key entry_4_9 = GramEntries.Block1.entries 4 9 := by
  decide +kernel

theorem entry_reindex_4_10 :
    Integer.Sparse.reindex key entry_4_10 = GramEntries.Block1.entries 4 10 := by
  decide +kernel

theorem entry_reindex_4_11 :
    Integer.Sparse.reindex key entry_4_11 = GramEntries.Block1.entries 4 11 := by
  decide +kernel

theorem entry_reindex_4_12 :
    Integer.Sparse.reindex key entry_4_12 = GramEntries.Block1.entries 4 12 := by
  decide +kernel

theorem entry_reindex_4_13 :
    Integer.Sparse.reindex key entry_4_13 = GramEntries.Block1.entries 4 13 := by
  decide +kernel

theorem entry_reindex_4_14 :
    Integer.Sparse.reindex key entry_4_14 = GramEntries.Block1.entries 4 14 := by
  decide +kernel

theorem entry_reindex_4_15 :
    Integer.Sparse.reindex key entry_4_15 = GramEntries.Block1.entries 4 15 := by
  decide +kernel

theorem entry_reindex_4_16 :
    Integer.Sparse.reindex key entry_4_16 = GramEntries.Block1.entries 4 16 := by
  decide +kernel

theorem entry_reindex_4_17 :
    Integer.Sparse.reindex key entry_4_17 = GramEntries.Block1.entries 4 17 := by
  decide +kernel

theorem entry_reindex_4_18 :
    Integer.Sparse.reindex key entry_4_18 = GramEntries.Block1.entries 4 18 := by
  decide +kernel

theorem entry_reindex_4_19 :
    Integer.Sparse.reindex key entry_4_19 = GramEntries.Block1.entries 4 19 := by
  decide +kernel

theorem entry_reindex_4_20 :
    Integer.Sparse.reindex key entry_4_20 = GramEntries.Block1.entries 4 20 := by
  decide +kernel

theorem entries_reindex_4 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 4 j) = GramEntries.Block1.entries 4 j := by
  fin_cases j
  · exact entry_reindex_4_0
  · exact entry_reindex_4_1
  · exact entry_reindex_4_2
  · exact entry_reindex_4_3
  · exact entry_reindex_4_4
  · exact entry_reindex_4_5
  · exact entry_reindex_4_6
  · exact entry_reindex_4_7
  · exact entry_reindex_4_8
  · exact entry_reindex_4_9
  · exact entry_reindex_4_10
  · exact entry_reindex_4_11
  · exact entry_reindex_4_12
  · exact entry_reindex_4_13
  · exact entry_reindex_4_14
  · exact entry_reindex_4_15
  · exact entry_reindex_4_16
  · exact entry_reindex_4_17
  · exact entry_reindex_4_18
  · exact entry_reindex_4_19
  · exact entry_reindex_4_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
