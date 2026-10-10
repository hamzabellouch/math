import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex0
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex1
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex2
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex3
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex4
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex5
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex6
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex7
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex8
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex9
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex10
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex11
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex12
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex13
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex14
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex15
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex16
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex17
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex18
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex19
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex20
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Reindex21

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entries_reindex (i j : Fin 22) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block4.entries i j := by
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
  · exact entries_reindex_12 j
  · exact entries_reindex_13 j
  · exact entries_reindex_14 j
  · exact entries_reindex_15 j
  · exact entries_reindex_16 j
  · exact entries_reindex_17 j
  · exact entries_reindex_18 j
  · exact entries_reindex_19 j
  · exact entries_reindex_20 j
  · exact entries_reindex_21 j

end MUB6.Certificate.GramAssembly.Block4

end OAI
