import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex0
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex1
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex2
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex3
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex4
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex5
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex6
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex7
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex8
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex9
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex10
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex11
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex12
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex13
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex14
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex15
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex16
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex17
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex18
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex19
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex20
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex21
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex22
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex23
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex24
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex25
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Reindex26

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entries_reindex (i j : Fin 27) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block3.entries i j := by
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
  · exact entries_reindex_22 j
  · exact entries_reindex_23 j
  · exact entries_reindex_24 j
  · exact entries_reindex_25 j
  · exact entries_reindex_26 j

end MUB6.Certificate.GramAssembly.Block3

end OAI
