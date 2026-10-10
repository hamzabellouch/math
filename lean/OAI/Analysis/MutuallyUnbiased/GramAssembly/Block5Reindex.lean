import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex0
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex1
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex2
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex3
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex4
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex5
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex6
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex7
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex8
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex9
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex10
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Reindex11

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entries_reindex (i j : Fin 12) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block5.entries i j := by
  fin_cases i
  · exact entries_reindex_0 j
  · exact entries_reindex_1 j
  · exact entries_reindex_2 j
  · exact entries_reindex_3 j
  · exact entries_reindex_4 j
  · exact entries_reindex_5 j
  · exact entries_reindex_6 j
  · exact entries_reindex_7 j
  · exact entries_reindex_8 j
  · exact entries_reindex_9 j
  · exact entries_reindex_10 j
  · exact entries_reindex_11 j

end MUB6.Certificate.GramAssembly.Block5

end OAI
