import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_8_0 :
    Integer.Sparse.reindex key entry_8_0 = GramEntries.Block1.entries 8 0 := by
  decide +kernel

theorem entry_reindex_8_1 :
    Integer.Sparse.reindex key entry_8_1 = GramEntries.Block1.entries 8 1 := by
  decide +kernel

theorem entry_reindex_8_2 :
    Integer.Sparse.reindex key entry_8_2 = GramEntries.Block1.entries 8 2 := by
  decide +kernel

theorem entry_reindex_8_3 :
    Integer.Sparse.reindex key entry_8_3 = GramEntries.Block1.entries 8 3 := by
  decide +kernel

theorem entry_reindex_8_4 :
    Integer.Sparse.reindex key entry_8_4 = GramEntries.Block1.entries 8 4 := by
  decide +kernel

theorem entry_reindex_8_5 :
    Integer.Sparse.reindex key entry_8_5 = GramEntries.Block1.entries 8 5 := by
  decide +kernel

theorem entry_reindex_8_6 :
    Integer.Sparse.reindex key entry_8_6 = GramEntries.Block1.entries 8 6 := by
  decide +kernel

theorem entry_reindex_8_7 :
    Integer.Sparse.reindex key entry_8_7 = GramEntries.Block1.entries 8 7 := by
  decide +kernel

theorem entry_reindex_8_8 :
    Integer.Sparse.reindex key entry_8_8 = GramEntries.Block1.entries 8 8 := by
  decide +kernel

theorem entry_reindex_8_9 :
    Integer.Sparse.reindex key entry_8_9 = GramEntries.Block1.entries 8 9 := by
  decide +kernel

theorem entry_reindex_8_10 :
    Integer.Sparse.reindex key entry_8_10 = GramEntries.Block1.entries 8 10 := by
  decide +kernel

theorem entry_reindex_8_11 :
    Integer.Sparse.reindex key entry_8_11 = GramEntries.Block1.entries 8 11 := by
  decide +kernel

theorem entry_reindex_8_12 :
    Integer.Sparse.reindex key entry_8_12 = GramEntries.Block1.entries 8 12 := by
  decide +kernel

theorem entry_reindex_8_13 :
    Integer.Sparse.reindex key entry_8_13 = GramEntries.Block1.entries 8 13 := by
  decide +kernel

theorem entry_reindex_8_14 :
    Integer.Sparse.reindex key entry_8_14 = GramEntries.Block1.entries 8 14 := by
  decide +kernel

theorem entry_reindex_8_15 :
    Integer.Sparse.reindex key entry_8_15 = GramEntries.Block1.entries 8 15 := by
  decide +kernel

theorem entry_reindex_8_16 :
    Integer.Sparse.reindex key entry_8_16 = GramEntries.Block1.entries 8 16 := by
  decide +kernel

theorem entry_reindex_8_17 :
    Integer.Sparse.reindex key entry_8_17 = GramEntries.Block1.entries 8 17 := by
  decide +kernel

theorem entry_reindex_8_18 :
    Integer.Sparse.reindex key entry_8_18 = GramEntries.Block1.entries 8 18 := by
  decide +kernel

theorem entry_reindex_8_19 :
    Integer.Sparse.reindex key entry_8_19 = GramEntries.Block1.entries 8 19 := by
  decide +kernel

theorem entry_reindex_8_20 :
    Integer.Sparse.reindex key entry_8_20 = GramEntries.Block1.entries 8 20 := by
  decide +kernel

theorem entries_reindex_8 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 8 j) = GramEntries.Block1.entries 8 j := by
  fin_cases j
  · exact entry_reindex_8_0
  · exact entry_reindex_8_1
  · exact entry_reindex_8_2
  · exact entry_reindex_8_3
  · exact entry_reindex_8_4
  · exact entry_reindex_8_5
  · exact entry_reindex_8_6
  · exact entry_reindex_8_7
  · exact entry_reindex_8_8
  · exact entry_reindex_8_9
  · exact entry_reindex_8_10
  · exact entry_reindex_8_11
  · exact entry_reindex_8_12
  · exact entry_reindex_8_13
  · exact entry_reindex_8_14
  · exact entry_reindex_8_15
  · exact entry_reindex_8_16
  · exact entry_reindex_8_17
  · exact entry_reindex_8_18
  · exact entry_reindex_8_19
  · exact entry_reindex_8_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
