import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex0
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex1
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex2
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex3
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex4
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex5
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex6
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex7
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex8
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex9
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Reindex10

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem entries_reindex (i j : Fin 11) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block2.entries i j := by
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

end MUB6.Certificate.GramAssembly.Block2

end OAI
