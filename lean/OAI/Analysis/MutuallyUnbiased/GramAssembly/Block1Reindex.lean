import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex0
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex1
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex2
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex3
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex4
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex5
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex6
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex7
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex8
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex9
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex10
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex11
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex12
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex13
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex14
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex15
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex16
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex17
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex18
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex19
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Reindex20

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem entries_reindex (i j : Fin 21) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block1.entries i j := by
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

end MUB6.Certificate.GramAssembly.Block1

end OAI
