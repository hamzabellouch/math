import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_2_0 :
    Integer.Sparse.reindex key entry_2_0 = GramEntries.Block1.entries 2 0 := by
  decide +kernel

theorem entry_reindex_2_1 :
    Integer.Sparse.reindex key entry_2_1 = GramEntries.Block1.entries 2 1 := by
  decide +kernel

theorem entry_reindex_2_2 :
    Integer.Sparse.reindex key entry_2_2 = GramEntries.Block1.entries 2 2 := by
  decide +kernel

theorem entry_reindex_2_3 :
    Integer.Sparse.reindex key entry_2_3 = GramEntries.Block1.entries 2 3 := by
  decide +kernel

theorem entry_reindex_2_4 :
    Integer.Sparse.reindex key entry_2_4 = GramEntries.Block1.entries 2 4 := by
  decide +kernel

theorem entry_reindex_2_5 :
    Integer.Sparse.reindex key entry_2_5 = GramEntries.Block1.entries 2 5 := by
  decide +kernel

theorem entry_reindex_2_6 :
    Integer.Sparse.reindex key entry_2_6 = GramEntries.Block1.entries 2 6 := by
  decide +kernel

theorem entry_reindex_2_7 :
    Integer.Sparse.reindex key entry_2_7 = GramEntries.Block1.entries 2 7 := by
  decide +kernel

theorem entry_reindex_2_8 :
    Integer.Sparse.reindex key entry_2_8 = GramEntries.Block1.entries 2 8 := by
  decide +kernel

theorem entry_reindex_2_9 :
    Integer.Sparse.reindex key entry_2_9 = GramEntries.Block1.entries 2 9 := by
  decide +kernel

theorem entry_reindex_2_10 :
    Integer.Sparse.reindex key entry_2_10 = GramEntries.Block1.entries 2 10 := by
  decide +kernel

theorem entry_reindex_2_11 :
    Integer.Sparse.reindex key entry_2_11 = GramEntries.Block1.entries 2 11 := by
  decide +kernel

theorem entry_reindex_2_12 :
    Integer.Sparse.reindex key entry_2_12 = GramEntries.Block1.entries 2 12 := by
  decide +kernel

theorem entry_reindex_2_13 :
    Integer.Sparse.reindex key entry_2_13 = GramEntries.Block1.entries 2 13 := by
  decide +kernel

theorem entry_reindex_2_14 :
    Integer.Sparse.reindex key entry_2_14 = GramEntries.Block1.entries 2 14 := by
  decide +kernel

theorem entry_reindex_2_15 :
    Integer.Sparse.reindex key entry_2_15 = GramEntries.Block1.entries 2 15 := by
  decide +kernel

theorem entry_reindex_2_16 :
    Integer.Sparse.reindex key entry_2_16 = GramEntries.Block1.entries 2 16 := by
  decide +kernel

theorem entry_reindex_2_17 :
    Integer.Sparse.reindex key entry_2_17 = GramEntries.Block1.entries 2 17 := by
  decide +kernel

theorem entry_reindex_2_18 :
    Integer.Sparse.reindex key entry_2_18 = GramEntries.Block1.entries 2 18 := by
  decide +kernel

theorem entry_reindex_2_19 :
    Integer.Sparse.reindex key entry_2_19 = GramEntries.Block1.entries 2 19 := by
  decide +kernel

theorem entry_reindex_2_20 :
    Integer.Sparse.reindex key entry_2_20 = GramEntries.Block1.entries 2 20 := by
  decide +kernel

theorem entries_reindex_2 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 2 j) = GramEntries.Block1.entries 2 j := by
  fin_cases j
  · exact entry_reindex_2_0
  · exact entry_reindex_2_1
  · exact entry_reindex_2_2
  · exact entry_reindex_2_3
  · exact entry_reindex_2_4
  · exact entry_reindex_2_5
  · exact entry_reindex_2_6
  · exact entry_reindex_2_7
  · exact entry_reindex_2_8
  · exact entry_reindex_2_9
  · exact entry_reindex_2_10
  · exact entry_reindex_2_11
  · exact entry_reindex_2_12
  · exact entry_reindex_2_13
  · exact entry_reindex_2_14
  · exact entry_reindex_2_15
  · exact entry_reindex_2_16
  · exact entry_reindex_2_17
  · exact entry_reindex_2_18
  · exact entry_reindex_2_19
  · exact entry_reindex_2_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
