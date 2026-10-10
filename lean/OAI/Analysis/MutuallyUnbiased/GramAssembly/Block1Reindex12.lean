import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entry_reindex_12_0 :
    Integer.Sparse.reindex key entry_12_0 = GramEntries.Block1.entries 12 0 := by
  decide +kernel

theorem entry_reindex_12_1 :
    Integer.Sparse.reindex key entry_12_1 = GramEntries.Block1.entries 12 1 := by
  decide +kernel

theorem entry_reindex_12_2 :
    Integer.Sparse.reindex key entry_12_2 = GramEntries.Block1.entries 12 2 := by
  decide +kernel

theorem entry_reindex_12_3 :
    Integer.Sparse.reindex key entry_12_3 = GramEntries.Block1.entries 12 3 := by
  decide +kernel

theorem entry_reindex_12_4 :
    Integer.Sparse.reindex key entry_12_4 = GramEntries.Block1.entries 12 4 := by
  decide +kernel

theorem entry_reindex_12_5 :
    Integer.Sparse.reindex key entry_12_5 = GramEntries.Block1.entries 12 5 := by
  decide +kernel

theorem entry_reindex_12_6 :
    Integer.Sparse.reindex key entry_12_6 = GramEntries.Block1.entries 12 6 := by
  decide +kernel

theorem entry_reindex_12_7 :
    Integer.Sparse.reindex key entry_12_7 = GramEntries.Block1.entries 12 7 := by
  decide +kernel

theorem entry_reindex_12_8 :
    Integer.Sparse.reindex key entry_12_8 = GramEntries.Block1.entries 12 8 := by
  decide +kernel

theorem entry_reindex_12_9 :
    Integer.Sparse.reindex key entry_12_9 = GramEntries.Block1.entries 12 9 := by
  decide +kernel

theorem entry_reindex_12_10 :
    Integer.Sparse.reindex key entry_12_10 = GramEntries.Block1.entries 12 10 := by
  decide +kernel

theorem entry_reindex_12_11 :
    Integer.Sparse.reindex key entry_12_11 = GramEntries.Block1.entries 12 11 := by
  decide +kernel

theorem entry_reindex_12_12 :
    Integer.Sparse.reindex key entry_12_12 = GramEntries.Block1.entries 12 12 := by
  decide +kernel

theorem entry_reindex_12_13 :
    Integer.Sparse.reindex key entry_12_13 = GramEntries.Block1.entries 12 13 := by
  decide +kernel

theorem entry_reindex_12_14 :
    Integer.Sparse.reindex key entry_12_14 = GramEntries.Block1.entries 12 14 := by
  decide +kernel

theorem entry_reindex_12_15 :
    Integer.Sparse.reindex key entry_12_15 = GramEntries.Block1.entries 12 15 := by
  decide +kernel

theorem entry_reindex_12_16 :
    Integer.Sparse.reindex key entry_12_16 = GramEntries.Block1.entries 12 16 := by
  decide +kernel

theorem entry_reindex_12_17 :
    Integer.Sparse.reindex key entry_12_17 = GramEntries.Block1.entries 12 17 := by
  decide +kernel

theorem entry_reindex_12_18 :
    Integer.Sparse.reindex key entry_12_18 = GramEntries.Block1.entries 12 18 := by
  decide +kernel

theorem entry_reindex_12_19 :
    Integer.Sparse.reindex key entry_12_19 = GramEntries.Block1.entries 12 19 := by
  decide +kernel

theorem entry_reindex_12_20 :
    Integer.Sparse.reindex key entry_12_20 = GramEntries.Block1.entries 12 20 := by
  decide +kernel

theorem entries_reindex_12 (j : Fin 21) :
    Integer.Sparse.reindex key (entries 12 j) = GramEntries.Block1.entries 12 j := by
  fin_cases j
  · exact entry_reindex_12_0
  · exact entry_reindex_12_1
  · exact entry_reindex_12_2
  · exact entry_reindex_12_3
  · exact entry_reindex_12_4
  · exact entry_reindex_12_5
  · exact entry_reindex_12_6
  · exact entry_reindex_12_7
  · exact entry_reindex_12_8
  · exact entry_reindex_12_9
  · exact entry_reindex_12_10
  · exact entry_reindex_12_11
  · exact entry_reindex_12_12
  · exact entry_reindex_12_13
  · exact entry_reindex_12_14
  · exact entry_reindex_12_15
  · exact entry_reindex_12_16
  · exact entry_reindex_12_17
  · exact entry_reindex_12_18
  · exact entry_reindex_12_19
  · exact entry_reindex_12_20

end MUB6.Certificate.GramAssembly.Block1

end OAI
