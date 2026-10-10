import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_3_0 :
    Integer.Sparse.reindex key entry_3_0 = GramEntries.Block1.entries 3 0 := by
  decide +kernel

theorem entry_reindex_3_1 :
    Integer.Sparse.reindex key entry_3_1 = GramEntries.Block1.entries 3 1 := by
  decide +kernel

theorem entry_reindex_3_2 :
    Integer.Sparse.reindex key entry_3_2 = GramEntries.Block1.entries 3 2 := by
  decide +kernel

theorem entry_reindex_3_3 :
    Integer.Sparse.reindex key entry_3_3 = GramEntries.Block1.entries 3 3 := by
  decide +kernel

theorem entry_reindex_3_4 :
    Integer.Sparse.reindex key entry_3_4 = GramEntries.Block1.entries 3 4 := by
  decide +kernel

theorem entry_reindex_3_5 :
    Integer.Sparse.reindex key entry_3_5 = GramEntries.Block1.entries 3 5 := by
  decide +kernel

theorem entry_reindex_3_6 :
    Integer.Sparse.reindex key entry_3_6 = GramEntries.Block1.entries 3 6 := by
  decide +kernel

theorem entry_reindex_3_7 :
    Integer.Sparse.reindex key entry_3_7 = GramEntries.Block1.entries 3 7 := by
  decide +kernel

theorem entry_reindex_3_8 :
    Integer.Sparse.reindex key entry_3_8 = GramEntries.Block1.entries 3 8 := by
  decide +kernel

theorem entry_reindex_3_9 :
    Integer.Sparse.reindex key entry_3_9 = GramEntries.Block1.entries 3 9 := by
  decide +kernel

theorem entry_reindex_3_10 :
    Integer.Sparse.reindex key entry_3_10 = GramEntries.Block1.entries 3 10 := by
  decide +kernel

theorem entry_reindex_3_11 :
    Integer.Sparse.reindex key entry_3_11 = GramEntries.Block1.entries 3 11 := by
  decide +kernel

theorem entry_reindex_3_12 :
    Integer.Sparse.reindex key entry_3_12 = GramEntries.Block1.entries 3 12 := by
  decide +kernel

theorem entry_reindex_3_13 :
    Integer.Sparse.reindex key entry_3_13 = GramEntries.Block1.entries 3 13 := by
  decide +kernel

theorem entry_reindex_3_14 :
    Integer.Sparse.reindex key entry_3_14 = GramEntries.Block1.entries 3 14 := by
  decide +kernel

theorem entry_reindex_3_15 :
    Integer.Sparse.reindex key entry_3_15 = GramEntries.Block1.entries 3 15 := by
  decide +kernel

theorem entry_reindex_3_16 :
    Integer.Sparse.reindex key entry_3_16 = GramEntries.Block1.entries 3 16 := by
  decide +kernel

theorem entry_reindex_3_17 :
    Integer.Sparse.reindex key entry_3_17 = GramEntries.Block1.entries 3 17 := by
  decide +kernel

theorem entry_reindex_3_18 :
    Integer.Sparse.reindex key entry_3_18 = GramEntries.Block1.entries 3 18 := by
  decide +kernel

theorem entry_reindex_3_19 :
    Integer.Sparse.reindex key entry_3_19 = GramEntries.Block1.entries 3 19 := by
  decide +kernel

theorem entry_reindex_3_20 :
    Integer.Sparse.reindex key entry_3_20 = GramEntries.Block1.entries 3 20 := by
  decide +kernel

theorem entries_reindex_3 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 3 j) = GramEntries.Block1.entries 3 j := by
  fin_cases j
  · exact entry_reindex_3_0
  · exact entry_reindex_3_1
  · exact entry_reindex_3_2
  · exact entry_reindex_3_3
  · exact entry_reindex_3_4
  · exact entry_reindex_3_5
  · exact entry_reindex_3_6
  · exact entry_reindex_3_7
  · exact entry_reindex_3_8
  · exact entry_reindex_3_9
  · exact entry_reindex_3_10
  · exact entry_reindex_3_11
  · exact entry_reindex_3_12
  · exact entry_reindex_3_13
  · exact entry_reindex_3_14
  · exact entry_reindex_3_15
  · exact entry_reindex_3_16
  · exact entry_reindex_3_17
  · exact entry_reindex_3_18
  · exact entry_reindex_3_19
  · exact entry_reindex_3_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
