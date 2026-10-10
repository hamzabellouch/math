import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0Data
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Data
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

theorem entry_reindex_2_0 :
    Integer.Sparse.reindex key entry_2_0 = GramEntries.Block0.entries 2 0 := by
  decide +kernel

theorem entry_reindex_2_1 :
    Integer.Sparse.reindex key entry_2_1 = GramEntries.Block0.entries 2 1 := by
  decide +kernel

theorem entry_reindex_2_2 :
    Integer.Sparse.reindex key entry_2_2 = GramEntries.Block0.entries 2 2 := by
  decide +kernel

theorem entry_reindex_2_3 :
    Integer.Sparse.reindex key entry_2_3 = GramEntries.Block0.entries 2 3 := by
  decide +kernel

theorem entry_reindex_2_4 :
    Integer.Sparse.reindex key entry_2_4 = GramEntries.Block0.entries 2 4 := by
  decide +kernel

theorem entries_reindex_2 (j : Fin 5) :
    Integer.Sparse.reindex key (entries 2 j) = GramEntries.Block0.entries 2 j := by
  fin_cases j
  · exact entry_reindex_2_0
  · exact entry_reindex_2_1
  · exact entry_reindex_2_2
  · exact entry_reindex_2_3
  · exact entry_reindex_2_4

end MUB6.Certificate.GramAssembly.Block0

end OAI
