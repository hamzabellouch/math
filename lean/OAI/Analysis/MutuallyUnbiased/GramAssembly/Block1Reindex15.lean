import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_15_0 :
    Integer.Sparse.reindex key entry_15_0 = GramEntries.Block1.entries 15 0 := by
  decide +kernel

theorem entry_reindex_15_1 :
    Integer.Sparse.reindex key entry_15_1 = GramEntries.Block1.entries 15 1 := by
  decide +kernel

theorem entry_reindex_15_2 :
    Integer.Sparse.reindex key entry_15_2 = GramEntries.Block1.entries 15 2 := by
  decide +kernel

theorem entry_reindex_15_3 :
    Integer.Sparse.reindex key entry_15_3 = GramEntries.Block1.entries 15 3 := by
  decide +kernel

theorem entry_reindex_15_4 :
    Integer.Sparse.reindex key entry_15_4 = GramEntries.Block1.entries 15 4 := by
  decide +kernel

theorem entry_reindex_15_5 :
    Integer.Sparse.reindex key entry_15_5 = GramEntries.Block1.entries 15 5 := by
  decide +kernel

theorem entry_reindex_15_6 :
    Integer.Sparse.reindex key entry_15_6 = GramEntries.Block1.entries 15 6 := by
  decide +kernel

theorem entry_reindex_15_7 :
    Integer.Sparse.reindex key entry_15_7 = GramEntries.Block1.entries 15 7 := by
  decide +kernel

theorem entry_reindex_15_8 :
    Integer.Sparse.reindex key entry_15_8 = GramEntries.Block1.entries 15 8 := by
  decide +kernel

theorem entry_reindex_15_9 :
    Integer.Sparse.reindex key entry_15_9 = GramEntries.Block1.entries 15 9 := by
  decide +kernel

theorem entry_reindex_15_10 :
    Integer.Sparse.reindex key entry_15_10 = GramEntries.Block1.entries 15 10 := by
  decide +kernel

theorem entry_reindex_15_11 :
    Integer.Sparse.reindex key entry_15_11 = GramEntries.Block1.entries 15 11 := by
  decide +kernel

theorem entry_reindex_15_12 :
    Integer.Sparse.reindex key entry_15_12 = GramEntries.Block1.entries 15 12 := by
  decide +kernel

theorem entry_reindex_15_13 :
    Integer.Sparse.reindex key entry_15_13 = GramEntries.Block1.entries 15 13 := by
  decide +kernel

theorem entry_reindex_15_14 :
    Integer.Sparse.reindex key entry_15_14 = GramEntries.Block1.entries 15 14 := by
  decide +kernel

theorem entry_reindex_15_15 :
    Integer.Sparse.reindex key entry_15_15 = GramEntries.Block1.entries 15 15 := by
  decide +kernel

theorem entry_reindex_15_16 :
    Integer.Sparse.reindex key entry_15_16 = GramEntries.Block1.entries 15 16 := by
  decide +kernel

theorem entry_reindex_15_17 :
    Integer.Sparse.reindex key entry_15_17 = GramEntries.Block1.entries 15 17 := by
  decide +kernel

theorem entry_reindex_15_18 :
    Integer.Sparse.reindex key entry_15_18 = GramEntries.Block1.entries 15 18 := by
  decide +kernel

theorem entry_reindex_15_19 :
    Integer.Sparse.reindex key entry_15_19 = GramEntries.Block1.entries 15 19 := by
  decide +kernel

theorem entry_reindex_15_20 :
    Integer.Sparse.reindex key entry_15_20 = GramEntries.Block1.entries 15 20 := by
  decide +kernel

theorem entries_reindex_15 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 15 j) = GramEntries.Block1.entries 15 j := by
  fin_cases j
  · exact entry_reindex_15_0
  · exact entry_reindex_15_1
  · exact entry_reindex_15_2
  · exact entry_reindex_15_3
  · exact entry_reindex_15_4
  · exact entry_reindex_15_5
  · exact entry_reindex_15_6
  · exact entry_reindex_15_7
  · exact entry_reindex_15_8
  · exact entry_reindex_15_9
  · exact entry_reindex_15_10
  · exact entry_reindex_15_11
  · exact entry_reindex_15_12
  · exact entry_reindex_15_13
  · exact entry_reindex_15_14
  · exact entry_reindex_15_15
  · exact entry_reindex_15_16
  · exact entry_reindex_15_17
  · exact entry_reindex_15_18
  · exact entry_reindex_15_19
  · exact entry_reindex_15_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
