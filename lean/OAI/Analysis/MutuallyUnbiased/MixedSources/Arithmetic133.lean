import OAI.Analysis.MutuallyUnbiased.MixedData.Source16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource2128 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1501 x + ((1 : ℝ) * Sparse.eval nodeValue1503 x + ((3 : ℝ) * Sparse.eval nodeValue1507 x + ((1 : ℝ) * Sparse.eval nodeValue1524 x + ((-1 : ℝ) * Sparse.eval nodeValue4057 x + 0))))

def numericRow2128 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1503, 1), (Sum.inr 1507, 3), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

theorem reindexCheck2128 : Integer.Sparse.reindex keyMap MixedData.row2128 = numericRow2128 := by decide +kernel

theorem numericCheck2128 (x : Master → ℝ) : Integer.Sparse.eval numericRow2128 x =
    (1 : ℝ) * reducedSource2128 x := by
  norm_num [numericRow2128, reducedSource2128, Integer.Sparse.eval, Sparse.eval, nodeValue1501, nodeValue1503, nodeValue1507, nodeValue1524, nodeValue4057]

noncomputable def reducedSource2129 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1504 x + ((1 : ℝ) * Sparse.eval nodeValue1507 x + ((1 : ℝ) * Sparse.eval nodeValue1508 x + ((3 : ℝ) * Sparse.eval nodeValue1517 x + ((-1 : ℝ) * Sparse.eval nodeValue4057 x + 0))))

def numericRow2129 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1507, 1), (Sum.inr 1508, 1), (Sum.inr 1517, 3), (Sum.inr 4057, -1)]

theorem reindexCheck2129 : Integer.Sparse.reindex keyMap MixedData.row2129 = numericRow2129 := by decide +kernel

theorem numericCheck2129 (x : Master → ℝ) : Integer.Sparse.eval numericRow2129 x =
    (1 : ℝ) * reducedSource2129 x := by
  norm_num [numericRow2129, reducedSource2129, Integer.Sparse.eval, Sparse.eval, nodeValue1504, nodeValue1507, nodeValue1508, nodeValue1517, nodeValue4057]

noncomputable def reducedSource2130 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1507 x + ((1 : ℝ) * Sparse.eval nodeValue1510 x + ((2 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1517 x + ((1 : ℝ) * Sparse.eval nodeValue1524 x + ((-1 : ℝ) * Sparse.eval nodeValue4057 x + 0)))))

def numericRow2130 : Integer.Sparse Master := [(Sum.inr 1507, 1), (Sum.inr 1510, 1), (Sum.inr 1512, 2), (Sum.inr 1517, 1), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

theorem reindexCheck2130 : Integer.Sparse.reindex keyMap MixedData.row2130 = numericRow2130 := by decide +kernel

theorem numericCheck2130 (x : Master → ℝ) : Integer.Sparse.eval numericRow2130 x =
    (1 : ℝ) * reducedSource2130 x := by
  norm_num [numericRow2130, reducedSource2130, Integer.Sparse.eval, Sparse.eval, nodeValue1507, nodeValue1510, nodeValue1512, nodeValue1517, nodeValue1524, nodeValue4057]

noncomputable def reducedSource2131 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue687 x + ((1 : ℝ) * Sparse.eval nodeValue1491 x + ((3 : ℝ) * Sparse.eval nodeValue1517 x + ((1 : ℝ) * Sparse.eval nodeValue1524 x + ((-1 : ℝ) * Sparse.eval nodeValue4057 x + 0))))

def numericRow2131 : Integer.Sparse Master := [(Sum.inr 1491, 1), (Sum.inr 1517, 3), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

theorem reindexCheck2131 : Integer.Sparse.reindex keyMap MixedData.row2131 = numericRow2131 := by decide +kernel

theorem numericCheck2131 (x : Master → ℝ) : Integer.Sparse.eval numericRow2131 x =
    (1 : ℝ) * reducedSource2131 x := by
  norm_num [numericRow2131, reducedSource2131, Integer.Sparse.eval, Sparse.eval, nodeValue687, nodeValue1491, nodeValue1517, nodeValue1524, nodeValue4057]

noncomputable def reducedSource2132 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1502 x + ((4 : ℝ) * Sparse.eval nodeValue1506 x + ((-1 : ℝ) * Sparse.eval nodeValue4056 x + 0))

def numericRow2132 : Integer.Sparse Master := [(Sum.inr 1502, 2), (Sum.inr 1506, 4), (Sum.inr 4056, -1)]

theorem reindexCheck2132 : Integer.Sparse.reindex keyMap MixedData.row2132 = numericRow2132 := by decide +kernel

theorem numericCheck2132 (x : Master → ℝ) : Integer.Sparse.eval numericRow2132 x =
    (1 : ℝ) * reducedSource2132 x := by
  norm_num [numericRow2132, reducedSource2132, Integer.Sparse.eval, Sparse.eval, nodeValue1502, nodeValue1506, nodeValue4056]

noncomputable def reducedSource2133 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue666 x + ((1 : ℝ) * Sparse.eval nodeValue1497 x + ((4 : ℝ) * Sparse.eval nodeValue1506 x + ((-1 : ℝ) * Sparse.eval nodeValue4056 x + 0)))

def numericRow2133 : Integer.Sparse Master := [(Sum.inr 1497, 1), (Sum.inr 1506, 4), (Sum.inr 4056, -1)]

theorem reindexCheck2133 : Integer.Sparse.reindex keyMap MixedData.row2133 = numericRow2133 := by decide +kernel

theorem numericCheck2133 (x : Master → ℝ) : Integer.Sparse.eval numericRow2133 x =
    (1 : ℝ) * reducedSource2133 x := by
  norm_num [numericRow2133, reducedSource2133, Integer.Sparse.eval, Sparse.eval, nodeValue666, nodeValue1497, nodeValue1506, nodeValue4056]

noncomputable def reducedSource2134 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1688 x + ((2 : ℝ) * Sparse.eval nodeValue1692 x + ((2 : ℝ) * Sparse.eval nodeValue1695 x + ((-1 : ℝ) * Sparse.eval nodeValue4066 x + 0)))

def numericRow2134 : Integer.Sparse Master := [(Sum.inr 1688, 2), (Sum.inr 1692, 2), (Sum.inr 1695, 2), (Sum.inr 4066, -1)]

theorem reindexCheck2134 : Integer.Sparse.reindex keyMap MixedData.row2134 = numericRow2134 := by decide +kernel

theorem numericCheck2134 (x : Master → ℝ) : Integer.Sparse.eval numericRow2134 x =
    (1 : ℝ) * reducedSource2134 x := by
  norm_num [numericRow2134, reducedSource2134, Integer.Sparse.eval, Sparse.eval, nodeValue1688, nodeValue1692, nodeValue1695, nodeValue4066]

noncomputable def reducedSource2135 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1692 x + ((2 : ℝ) * Sparse.eval nodeValue3262 x + ((2 : ℝ) * Sparse.eval nodeValue3275 x + ((-1 : ℝ) * Sparse.eval nodeValue4066 x + 0)))

def numericRow2135 : Integer.Sparse Master := [(Sum.inr 1692, 2), (Sum.inr 3262, 2), (Sum.inr 3275, 2), (Sum.inr 4066, -1)]

theorem reindexCheck2135 : Integer.Sparse.reindex keyMap MixedData.row2135 = numericRow2135 := by decide +kernel

theorem numericCheck2135 (x : Master → ℝ) : Integer.Sparse.eval numericRow2135 x =
    (1 : ℝ) * reducedSource2135 x := by
  norm_num [numericRow2135, reducedSource2135, Integer.Sparse.eval, Sparse.eval, nodeValue1692, nodeValue3262, nodeValue3275, nodeValue4066]

noncomputable def reducedSource2136 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1685 x + ((1 : ℝ) * Sparse.eval nodeValue1687 x + ((1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue1743 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

def numericRow2136 : Integer.Sparse Master := [(Sum.inr 1685, 2), (Sum.inr 1687, 1), (Sum.inr 1694, 1), (Sum.inr 1743, 1), (Sum.inr 2167, 1), (Sum.inr 4067, -1)]

theorem reindexCheck2136 : Integer.Sparse.reindex keyMap MixedData.row2136 = numericRow2136 := by decide +kernel

theorem numericCheck2136 (x : Master → ℝ) : Integer.Sparse.eval numericRow2136 x =
    (1 : ℝ) * reducedSource2136 x := by
  norm_num [numericRow2136, reducedSource2136, Integer.Sparse.eval, Sparse.eval, nodeValue1685, nodeValue1687, nodeValue1694, nodeValue1743, nodeValue2167, nodeValue4067]

noncomputable def reducedSource2137 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1679 x + ((1 : ℝ) * Sparse.eval nodeValue1683 x + ((1 : ℝ) * Sparse.eval nodeValue1693 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

def numericRow2137 : Integer.Sparse Master := [(Sum.inr 1679, 2), (Sum.inr 1683, 1), (Sum.inr 1693, 1), (Sum.inr 1735, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem reindexCheck2137 : Integer.Sparse.reindex keyMap MixedData.row2137 = numericRow2137 := by decide +kernel

theorem numericCheck2137 (x : Master → ℝ) : Integer.Sparse.eval numericRow2137 x =
    (1 : ℝ) * reducedSource2137 x := by
  norm_num [numericRow2137, reducedSource2137, Integer.Sparse.eval, Sparse.eval, nodeValue1679, nodeValue1683, nodeValue1693, nodeValue1735, nodeValue3277, nodeValue4067]

noncomputable def reducedSource2138 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1693 x + ((1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

def numericRow2138 : Integer.Sparse Master := [(Sum.inr 1689, 2), (Sum.inr 1693, 1), (Sum.inr 1694, 1), (Sum.inr 1748, 1), (Sum.inr 3276, 1), (Sum.inr 4067, -1)]

theorem reindexCheck2138 : Integer.Sparse.reindex keyMap MixedData.row2138 = numericRow2138 := by decide +kernel

theorem numericCheck2138 (x : Master → ℝ) : Integer.Sparse.eval numericRow2138 x =
    (1 : ℝ) * reducedSource2138 x := by
  norm_num [numericRow2138, reducedSource2138, Integer.Sparse.eval, Sparse.eval, nodeValue1689, nodeValue1693, nodeValue1694, nodeValue1748, nodeValue3276, nodeValue4067]

noncomputable def reducedSource2139 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1683 x + ((2 : ℝ) * Sparse.eval nodeValue2149 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((1 : ℝ) * Sparse.eval nodeValue2258 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

def numericRow2139 : Integer.Sparse Master := [(Sum.inr 1683, 1), (Sum.inr 2149, 2), (Sum.inr 2167, 1), (Sum.inr 2258, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem reindexCheck2139 : Integer.Sparse.reindex keyMap MixedData.row2139 = numericRow2139 := by decide +kernel

theorem numericCheck2139 (x : Master → ℝ) : Integer.Sparse.eval numericRow2139 x =
    (1 : ℝ) * reducedSource2139 x := by
  norm_num [numericRow2139, reducedSource2139, Integer.Sparse.eval, Sparse.eval, nodeValue1683, nodeValue2149, nodeValue2167, nodeValue2258, nodeValue3277, nodeValue4067]

noncomputable def reducedSource2140 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((2 : ℝ) * Sparse.eval nodeValue3268 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

def numericRow2140 : Integer.Sparse Master := [(Sum.inr 1694, 1), (Sum.inr 2167, 1), (Sum.inr 3268, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem reindexCheck2140 : Integer.Sparse.reindex keyMap MixedData.row2140 = numericRow2140 := by decide +kernel

theorem numericCheck2140 (x : Master → ℝ) : Integer.Sparse.eval numericRow2140 x =
    (1 : ℝ) * reducedSource2140 x := by
  norm_num [numericRow2140, reducedSource2140, Integer.Sparse.eval, Sparse.eval, nodeValue1694, nodeValue2167, nodeValue3268, nodeValue3276, nodeValue3277, nodeValue4067]

noncomputable def reducedSource2141 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1693 x + ((2 : ℝ) * Sparse.eval nodeValue3272 x + ((2 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0))))

def numericRow2141 : Integer.Sparse Master := [(Sum.inr 1693, 1), (Sum.inr 3272, 2), (Sum.inr 3276, 2), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem reindexCheck2141 : Integer.Sparse.reindex keyMap MixedData.row2141 = numericRow2141 := by decide +kernel

theorem numericCheck2141 (x : Master → ℝ) : Integer.Sparse.eval numericRow2141 x =
    (1 : ℝ) * reducedSource2141 x := by
  norm_num [numericRow2141, reducedSource2141, Integer.Sparse.eval, Sparse.eval, nodeValue1693, nodeValue3272, nodeValue3276, nodeValue3277, nodeValue4067]

noncomputable def reducedSource2142 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1579 x + ((1 : ℝ) * Sparse.eval nodeValue3237 x + ((2 : ℝ) * Sparse.eval nodeValue3252 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

def numericRow2142 : Integer.Sparse Master := [(Sum.inr 3237, 1), (Sum.inr 3252, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem reindexCheck2142 : Integer.Sparse.reindex keyMap MixedData.row2142 = numericRow2142 := by decide +kernel

theorem numericCheck2142 (x : Master → ℝ) : Integer.Sparse.eval numericRow2142 x =
    (1 : ℝ) * reducedSource2142 x := by
  norm_num [numericRow2142, reducedSource2142, Integer.Sparse.eval, Sparse.eval, nodeValue1579, nodeValue3237, nodeValue3252, nodeValue3276, nodeValue3277, nodeValue4067]

noncomputable def reducedSource2143 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1576 x + ((2 : ℝ) * Sparse.eval nodeValue1849 x + ((1 : ℝ) * Sparse.eval nodeValue1858 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

def numericRow2143 : Integer.Sparse Master := [(Sum.inr 1849, 2), (Sum.inr 1858, 1), (Sum.inr 2167, 1), (Sum.inr 3276, 1), (Sum.inr 4067, -1)]

theorem reindexCheck2143 : Integer.Sparse.reindex keyMap MixedData.row2143 = numericRow2143 := by decide +kernel

theorem numericCheck2143 (x : Master → ℝ) : Integer.Sparse.eval numericRow2143 x =
    (1 : ℝ) * reducedSource2143 x := by
  norm_num [numericRow2143, reducedSource2143, Integer.Sparse.eval, Sparse.eval, nodeValue1576, nodeValue1849, nodeValue1858, nodeValue2167, nodeValue3276, nodeValue4067]

end MUB6.Certificate.MixedSourceBridge

end OAI
