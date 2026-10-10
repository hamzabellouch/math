import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_20_0 :
    Integer.Sparse.reindex key entry_20_0 = GramEntries.Block1.entries 20 0 := by
  decide +kernel

theorem entry_reindex_20_1 :
    Integer.Sparse.reindex key entry_20_1 = GramEntries.Block1.entries 20 1 := by
  decide +kernel

theorem entry_reindex_20_2 :
    Integer.Sparse.reindex key entry_20_2 = GramEntries.Block1.entries 20 2 := by
  decide +kernel

theorem entry_reindex_20_3 :
    Integer.Sparse.reindex key entry_20_3 = GramEntries.Block1.entries 20 3 := by
  decide +kernel

theorem entry_reindex_20_4 :
    Integer.Sparse.reindex key entry_20_4 = GramEntries.Block1.entries 20 4 := by
  decide +kernel

theorem entry_reindex_20_5 :
    Integer.Sparse.reindex key entry_20_5 = GramEntries.Block1.entries 20 5 := by
  decide +kernel

theorem entry_reindex_20_6 :
    Integer.Sparse.reindex key entry_20_6 = GramEntries.Block1.entries 20 6 := by
  decide +kernel

theorem entry_reindex_20_7 :
    Integer.Sparse.reindex key entry_20_7 = GramEntries.Block1.entries 20 7 := by
  decide +kernel

theorem entry_reindex_20_8 :
    Integer.Sparse.reindex key entry_20_8 = GramEntries.Block1.entries 20 8 := by
  decide +kernel

theorem entry_reindex_20_9 :
    Integer.Sparse.reindex key entry_20_9 = GramEntries.Block1.entries 20 9 := by
  decide +kernel

theorem entry_reindex_20_10 :
    Integer.Sparse.reindex key entry_20_10 = GramEntries.Block1.entries 20 10 := by
  decide +kernel

theorem entry_reindex_20_11 :
    Integer.Sparse.reindex key entry_20_11 = GramEntries.Block1.entries 20 11 := by
  decide +kernel

theorem entry_reindex_20_12 :
    Integer.Sparse.reindex key entry_20_12 = GramEntries.Block1.entries 20 12 := by
  decide +kernel

theorem entry_reindex_20_13 :
    Integer.Sparse.reindex key entry_20_13 = GramEntries.Block1.entries 20 13 := by
  decide +kernel

theorem entry_reindex_20_14 :
    Integer.Sparse.reindex key entry_20_14 = GramEntries.Block1.entries 20 14 := by
  decide +kernel

theorem entry_reindex_20_15 :
    Integer.Sparse.reindex key entry_20_15 = GramEntries.Block1.entries 20 15 := by
  decide +kernel

theorem entry_reindex_20_16 :
    Integer.Sparse.reindex key entry_20_16 = GramEntries.Block1.entries 20 16 := by
  decide +kernel

theorem entry_reindex_20_17 :
    Integer.Sparse.reindex key entry_20_17 = GramEntries.Block1.entries 20 17 := by
  decide +kernel

theorem entry_reindex_20_18 :
    Integer.Sparse.reindex key entry_20_18 = GramEntries.Block1.entries 20 18 := by
  decide +kernel

theorem entry_reindex_20_19 :
    Integer.Sparse.reindex key entry_20_19 = GramEntries.Block1.entries 20 19 := by
  decide +kernel

theorem entry_reindex_20_20 :
    Integer.Sparse.reindex key entry_20_20 = GramEntries.Block1.entries 20 20 := by
  decide +kernel

theorem entries_reindex_20 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 20 j) = GramEntries.Block1.entries 20 j := by
  fin_cases j
  · exact entry_reindex_20_0
  · exact entry_reindex_20_1
  · exact entry_reindex_20_2
  · exact entry_reindex_20_3
  · exact entry_reindex_20_4
  · exact entry_reindex_20_5
  · exact entry_reindex_20_6
  · exact entry_reindex_20_7
  · exact entry_reindex_20_8
  · exact entry_reindex_20_9
  · exact entry_reindex_20_10
  · exact entry_reindex_20_11
  · exact entry_reindex_20_12
  · exact entry_reindex_20_13
  · exact entry_reindex_20_14
  · exact entry_reindex_20_15
  · exact entry_reindex_20_16
  · exact entry_reindex_20_17
  · exact entry_reindex_20_18
  · exact entry_reindex_20_19
  · exact entry_reindex_20_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
