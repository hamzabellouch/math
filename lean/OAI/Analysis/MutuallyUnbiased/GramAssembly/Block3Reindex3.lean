import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_3_0 :
    Integer.Sparse.reindex key entry_3_0 = GramEntries.Block3.entries 3 0 := by
  decide +kernel

theorem entry_reindex_3_1 :
    Integer.Sparse.reindex key entry_3_1 = GramEntries.Block3.entries 3 1 := by
  decide +kernel

theorem entry_reindex_3_2 :
    Integer.Sparse.reindex key entry_3_2 = GramEntries.Block3.entries 3 2 := by
  decide +kernel

theorem entry_reindex_3_3 :
    Integer.Sparse.reindex key entry_3_3 = GramEntries.Block3.entries 3 3 := by
  decide +kernel

theorem entry_reindex_3_4 :
    Integer.Sparse.reindex key entry_3_4 = GramEntries.Block3.entries 3 4 := by
  decide +kernel

theorem entry_reindex_3_5 :
    Integer.Sparse.reindex key entry_3_5 = GramEntries.Block3.entries 3 5 := by
  decide +kernel

theorem entry_reindex_3_6 :
    Integer.Sparse.reindex key entry_3_6 = GramEntries.Block3.entries 3 6 := by
  decide +kernel

theorem entry_reindex_3_7 :
    Integer.Sparse.reindex key entry_3_7 = GramEntries.Block3.entries 3 7 := by
  decide +kernel

theorem entry_reindex_3_8 :
    Integer.Sparse.reindex key entry_3_8 = GramEntries.Block3.entries 3 8 := by
  decide +kernel

theorem entry_reindex_3_9 :
    Integer.Sparse.reindex key entry_3_9 = GramEntries.Block3.entries 3 9 := by
  decide +kernel

theorem entry_reindex_3_10 :
    Integer.Sparse.reindex key entry_3_10 = GramEntries.Block3.entries 3 10 := by
  decide +kernel

theorem entry_reindex_3_11 :
    Integer.Sparse.reindex key entry_3_11 = GramEntries.Block3.entries 3 11 := by
  decide +kernel

theorem entry_reindex_3_12 :
    Integer.Sparse.reindex key entry_3_12 = GramEntries.Block3.entries 3 12 := by
  decide +kernel

theorem entry_reindex_3_13 :
    Integer.Sparse.reindex key entry_3_13 = GramEntries.Block3.entries 3 13 := by
  decide +kernel

theorem entry_reindex_3_14 :
    Integer.Sparse.reindex key entry_3_14 = GramEntries.Block3.entries 3 14 := by
  decide +kernel

theorem entry_reindex_3_15 :
    Integer.Sparse.reindex key entry_3_15 = GramEntries.Block3.entries 3 15 := by
  decide +kernel

theorem entry_reindex_3_16 :
    Integer.Sparse.reindex key entry_3_16 = GramEntries.Block3.entries 3 16 := by
  decide +kernel

theorem entry_reindex_3_17 :
    Integer.Sparse.reindex key entry_3_17 = GramEntries.Block3.entries 3 17 := by
  decide +kernel

theorem entry_reindex_3_18 :
    Integer.Sparse.reindex key entry_3_18 = GramEntries.Block3.entries 3 18 := by
  decide +kernel

theorem entry_reindex_3_19 :
    Integer.Sparse.reindex key entry_3_19 = GramEntries.Block3.entries 3 19 := by
  decide +kernel

theorem entry_reindex_3_20 :
    Integer.Sparse.reindex key entry_3_20 = GramEntries.Block3.entries 3 20 := by
  decide +kernel

theorem entry_reindex_3_21 :
    Integer.Sparse.reindex key entry_3_21 = GramEntries.Block3.entries 3 21 := by
  decide +kernel

theorem entry_reindex_3_22 :
    Integer.Sparse.reindex key entry_3_22 = GramEntries.Block3.entries 3 22 := by
  decide +kernel

theorem entry_reindex_3_23 :
    Integer.Sparse.reindex key entry_3_23 = GramEntries.Block3.entries 3 23 := by
  decide +kernel

theorem entry_reindex_3_24 :
    Integer.Sparse.reindex key entry_3_24 = GramEntries.Block3.entries 3 24 := by
  decide +kernel

theorem entry_reindex_3_25 :
    Integer.Sparse.reindex key entry_3_25 = GramEntries.Block3.entries 3 25 := by
  decide +kernel

theorem entry_reindex_3_26 :
    Integer.Sparse.reindex key entry_3_26 = GramEntries.Block3.entries 3 26 := by
  decide +kernel

theorem entries_reindex_3 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 3 j) = GramEntries.Block3.entries 3 j := by
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
  · exact entry_reindex_3_21
  · exact entry_reindex_3_22
  · exact entry_reindex_3_23
  · exact entry_reindex_3_24
  · exact entry_reindex_3_25
  · exact entry_reindex_3_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
