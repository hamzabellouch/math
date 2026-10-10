import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0Reindex0
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0Reindex1
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0Reindex2
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0Reindex3
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0Reindex4

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

theorem entries_reindex (i j : Fin 5) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block0.entries i j := by
  fin_cases i
  · exact entries_reindex_0 j
  · exact entries_reindex_1 j
  · exact entries_reindex_2 j
  · exact entries_reindex_3 j
  · exact entries_reindex_4 j

end MUB6.Certificate.GramAssembly.Block0

end OAI
