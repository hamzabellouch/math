import OAI.Analysis.MutuallyUnbiased.MixedData.Source16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource2112 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1534 x + ((2 : ℝ) * Sparse.eval nodeValue1541 x + ((-1 : ℝ) * Sparse.eval nodeValue4062 x + 0))

def numericRow2112 : Integer.Sparse Master := [(Sum.inr 1534, 4), (Sum.inr 1541, 2), (Sum.inr 4062, -1)]

theorem reindexCheck2112 : Integer.Sparse.reindex keyMap MixedData.row2112 = numericRow2112 := by decide +kernel

theorem numericCheck2112 (x : Master → ℝ) : Integer.Sparse.eval numericRow2112 x =
    (1 : ℝ) * reducedSource2112 x := by
  norm_num [numericRow2112, reducedSource2112, Integer.Sparse.eval, Sparse.eval, nodeValue1534, nodeValue1541, nodeValue4062]

noncomputable def reducedSource2113 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue686 x + ((1 : ℝ) * Sparse.eval nodeValue697 x + ((1 : ℝ) * Sparse.eval nodeValue1541 x + ((-1 : ℝ) * Sparse.eval nodeValue4062 x + 0)))

def numericRow2113 : Integer.Sparse Master := [(Sum.inr 686, 4), (Sum.inr 1541, 1), (Sum.inr 4062, -1)]

theorem reindexCheck2113 : Integer.Sparse.reindex keyMap MixedData.row2113 = numericRow2113 := by decide +kernel

theorem numericCheck2113 (x : Master → ℝ) : Integer.Sparse.eval numericRow2113 x =
    (1 : ℝ) * reducedSource2113 x := by
  norm_num [numericRow2113, reducedSource2113, Integer.Sparse.eval, Sparse.eval, nodeValue686, nodeValue697, nodeValue1541, nodeValue4062]

noncomputable def reducedSource2114 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1521 x + ((3 : ℝ) * Sparse.eval nodeValue1532 x + ((1 : ℝ) * Sparse.eval nodeValue1537 x + ((1 : ℝ) * Sparse.eval nodeValue1540 x + ((-1 : ℝ) * Sparse.eval nodeValue4060 x + 0))))

def numericRow2114 : Integer.Sparse Master := [(Sum.inr 1521, 1), (Sum.inr 1532, 3), (Sum.inr 1537, 1), (Sum.inr 1540, 1), (Sum.inr 4060, -1)]

theorem reindexCheck2114 : Integer.Sparse.reindex keyMap MixedData.row2114 = numericRow2114 := by decide +kernel

theorem numericCheck2114 (x : Master → ℝ) : Integer.Sparse.eval numericRow2114 x =
    (1 : ℝ) * reducedSource2114 x := by
  norm_num [numericRow2114, reducedSource2114, Integer.Sparse.eval, Sparse.eval, nodeValue1521, nodeValue1532, nodeValue1537, nodeValue1540, nodeValue4060]

noncomputable def reducedSource2115 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1516 x + ((1 : ℝ) * Sparse.eval nodeValue1521 x + ((2 : ℝ) * Sparse.eval nodeValue1537 x + ((-1 : ℝ) * Sparse.eval nodeValue4060 x + 0)))

def numericRow2115 : Integer.Sparse Master := [(Sum.inr 1516, 3), (Sum.inr 1521, 1), (Sum.inr 1537, 2), (Sum.inr 4060, -1)]

theorem reindexCheck2115 : Integer.Sparse.reindex keyMap MixedData.row2115 = numericRow2115 := by decide +kernel

theorem numericCheck2115 (x : Master → ℝ) : Integer.Sparse.eval numericRow2115 x =
    (1 : ℝ) * reducedSource2115 x := by
  norm_num [numericRow2115, reducedSource2115, Integer.Sparse.eval, Sparse.eval, nodeValue1516, nodeValue1521, nodeValue1537, nodeValue4060]

noncomputable def reducedSource2116 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue683 x + ((1 : ℝ) * Sparse.eval nodeValue691 x + ((1 : ℝ) * Sparse.eval nodeValue695 x + ((1 : ℝ) * Sparse.eval nodeValue1537 x + ((-1 : ℝ) * Sparse.eval nodeValue4060 x + 0))))

def numericRow2116 : Integer.Sparse Master := [(Sum.inr 683, 3), (Sum.inr 695, 1), (Sum.inr 1537, 1), (Sum.inr 4060, -1)]

theorem reindexCheck2116 : Integer.Sparse.reindex keyMap MixedData.row2116 = numericRow2116 := by decide +kernel

theorem numericCheck2116 (x : Master → ℝ) : Integer.Sparse.eval numericRow2116 x =
    (1 : ℝ) * reducedSource2116 x := by
  norm_num [numericRow2116, reducedSource2116, Integer.Sparse.eval, Sparse.eval, nodeValue683, nodeValue691, nodeValue695, nodeValue1537, nodeValue4060]

noncomputable def reducedSource2117 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1527 x + ((3 : ℝ) * Sparse.eval nodeValue1529 x + ((1 : ℝ) * Sparse.eval nodeValue1531 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0))))

def numericRow2117 : Integer.Sparse Master := [(Sum.inr 1527, 1), (Sum.inr 1529, 3), (Sum.inr 1531, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

theorem reindexCheck2117 : Integer.Sparse.reindex keyMap MixedData.row2117 = numericRow2117 := by decide +kernel

theorem numericCheck2117 (x : Master → ℝ) : Integer.Sparse.eval numericRow2117 x =
    (1 : ℝ) * reducedSource2117 x := by
  norm_num [numericRow2117, reducedSource2117, Integer.Sparse.eval, Sparse.eval, nodeValue1527, nodeValue1529, nodeValue1531, nodeValue1539, nodeValue4061]

noncomputable def reducedSource2118 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1523 x + ((1 : ℝ) * Sparse.eval nodeValue1527 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0))))

def numericRow2118 : Integer.Sparse Master := [(Sum.inr 1523, 3), (Sum.inr 1527, 1), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

theorem reindexCheck2118 : Integer.Sparse.reindex keyMap MixedData.row2118 = numericRow2118 := by decide +kernel

theorem numericCheck2118 (x : Master → ℝ) : Integer.Sparse.eval numericRow2118 x =
    (1 : ℝ) * reducedSource2118 x := by
  norm_num [numericRow2118, reducedSource2118, Integer.Sparse.eval, Sparse.eval, nodeValue1523, nodeValue1527, nodeValue1538, nodeValue1539, nodeValue4061]

noncomputable def reducedSource2119 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1533 x + ((2 : ℝ) * Sparse.eval nodeValue1538 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0)))

def numericRow2119 : Integer.Sparse Master := [(Sum.inr 1533, 3), (Sum.inr 1538, 2), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

theorem reindexCheck2119 : Integer.Sparse.reindex keyMap MixedData.row2119 = numericRow2119 := by decide +kernel

theorem numericCheck2119 (x : Master → ℝ) : Integer.Sparse.eval numericRow2119 x =
    (1 : ℝ) * reducedSource2119 x := by
  norm_num [numericRow2119, reducedSource2119, Integer.Sparse.eval, Sparse.eval, nodeValue1533, nodeValue1538, nodeValue1539, nodeValue4061]

noncomputable def reducedSource2120 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue696 x + ((3 : ℝ) * Sparse.eval nodeValue1496 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0))))

def numericRow2120 : Integer.Sparse Master := [(Sum.inr 1496, 3), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

theorem reindexCheck2120 : Integer.Sparse.reindex keyMap MixedData.row2120 = numericRow2120 := by decide +kernel

theorem numericCheck2120 (x : Master → ℝ) : Integer.Sparse.eval numericRow2120 x =
    (1 : ℝ) * reducedSource2120 x := by
  norm_num [numericRow2120, reducedSource2120, Integer.Sparse.eval, Sparse.eval, nodeValue696, nodeValue1496, nodeValue1538, nodeValue1539, nodeValue4061]

noncomputable def reducedSource2121 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue693 x + ((3 : ℝ) * Sparse.eval nodeValue1495 x + ((1 : ℝ) * Sparse.eval nodeValue1527 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0))))

def numericRow2121 : Integer.Sparse Master := [(Sum.inr 1495, 3), (Sum.inr 1527, 1), (Sum.inr 1538, 1), (Sum.inr 4061, -1)]

theorem reindexCheck2121 : Integer.Sparse.reindex keyMap MixedData.row2121 = numericRow2121 := by decide +kernel

theorem numericCheck2121 (x : Master → ℝ) : Integer.Sparse.eval numericRow2121 x =
    (1 : ℝ) * reducedSource2121 x := by
  norm_num [numericRow2121, reducedSource2121, Integer.Sparse.eval, Sparse.eval, nodeValue693, nodeValue1495, nodeValue1527, nodeValue1538, nodeValue4061]

noncomputable def reducedSource2122 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1514 x + ((2 : ℝ) * Sparse.eval nodeValue1518 x + ((1 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1535 x + ((-1 : ℝ) * Sparse.eval nodeValue4058 x + 0))))

def numericRow2122 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1518, 2), (Sum.inr 1520, 1), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

theorem reindexCheck2122 : Integer.Sparse.reindex keyMap MixedData.row2122 = numericRow2122 := by decide +kernel

theorem numericCheck2122 (x : Master → ℝ) : Integer.Sparse.eval numericRow2122 x =
    (1 : ℝ) * reducedSource2122 x := by
  norm_num [numericRow2122, reducedSource2122, Integer.Sparse.eval, Sparse.eval, nodeValue1514, nodeValue1518, nodeValue1520, nodeValue1535, nodeValue4058]

noncomputable def reducedSource2123 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1509 x + ((2 : ℝ) * Sparse.eval nodeValue1528 x + ((2 : ℝ) * Sparse.eval nodeValue1530 x + ((1 : ℝ) * Sparse.eval nodeValue1535 x + ((-1 : ℝ) * Sparse.eval nodeValue4058 x + 0))))

def numericRow2123 : Integer.Sparse Master := [(Sum.inr 1509, 1), (Sum.inr 1528, 2), (Sum.inr 1530, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

theorem reindexCheck2123 : Integer.Sparse.reindex keyMap MixedData.row2123 = numericRow2123 := by decide +kernel

theorem numericCheck2123 (x : Master → ℝ) : Integer.Sparse.eval numericRow2123 x =
    (1 : ℝ) * reducedSource2123 x := by
  norm_num [numericRow2123, reducedSource2123, Integer.Sparse.eval, Sparse.eval, nodeValue1509, nodeValue1528, nodeValue1530, nodeValue1535, nodeValue4058]

noncomputable def reducedSource2124 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1505 x + ((1 : ℝ) * Sparse.eval nodeValue1509 x + ((2 : ℝ) * Sparse.eval nodeValue1518 x + ((1 : ℝ) * Sparse.eval nodeValue1535 x + ((-1 : ℝ) * Sparse.eval nodeValue4058 x + 0))))

def numericRow2124 : Integer.Sparse Master := [(Sum.inr 1505, 2), (Sum.inr 1509, 1), (Sum.inr 1518, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

theorem reindexCheck2124 : Integer.Sparse.reindex keyMap MixedData.row2124 = numericRow2124 := by decide +kernel

theorem numericCheck2124 (x : Master → ℝ) : Integer.Sparse.eval numericRow2124 x =
    (1 : ℝ) * reducedSource2124 x := by
  norm_num [numericRow2124, reducedSource2124, Integer.Sparse.eval, Sparse.eval, nodeValue1505, nodeValue1509, nodeValue1518, nodeValue1535, nodeValue4058]

noncomputable def reducedSource2125 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1511 x + ((1 : ℝ) * Sparse.eval nodeValue1513 x + ((1 : ℝ) * Sparse.eval nodeValue1519 x + ((2 : ℝ) * Sparse.eval nodeValue1525 x + ((-1 : ℝ) * Sparse.eval nodeValue4059 x + 0))))

def numericRow2125 : Integer.Sparse Master := [(Sum.inr 1511, 2), (Sum.inr 1513, 1), (Sum.inr 1519, 1), (Sum.inr 1525, 2), (Sum.inr 4059, -1)]

theorem reindexCheck2125 : Integer.Sparse.reindex keyMap MixedData.row2125 = numericRow2125 := by decide +kernel

theorem numericCheck2125 (x : Master → ℝ) : Integer.Sparse.eval numericRow2125 x =
    (1 : ℝ) * reducedSource2125 x := by
  norm_num [numericRow2125, reducedSource2125, Integer.Sparse.eval, Sparse.eval, nodeValue1511, nodeValue1513, nodeValue1519, nodeValue1525, nodeValue4059]

noncomputable def reducedSource2126 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1519 x + ((2 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue1525 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((1 : ℝ) * Sparse.eval nodeValue1536 x + ((-1 : ℝ) * Sparse.eval nodeValue4059 x + 0)))))

def numericRow2126 : Integer.Sparse Master := [(Sum.inr 1519, 1), (Sum.inr 1522, 2), (Sum.inr 1525, 1), (Sum.inr 1526, 1), (Sum.inr 1536, 1), (Sum.inr 4059, -1)]

theorem reindexCheck2126 : Integer.Sparse.reindex keyMap MixedData.row2126 = numericRow2126 := by decide +kernel

theorem numericCheck2126 (x : Master → ℝ) : Integer.Sparse.eval numericRow2126 x =
    (1 : ℝ) * reducedSource2126 x := by
  norm_num [numericRow2126, reducedSource2126, Integer.Sparse.eval, Sparse.eval, nodeValue1519, nodeValue1522, nodeValue1525, nodeValue1526, nodeValue1536, nodeValue4059]

noncomputable def reducedSource2127 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1515 x + ((2 : ℝ) * Sparse.eval nodeValue1519 x + ((2 : ℝ) * Sparse.eval nodeValue1536 x + ((-1 : ℝ) * Sparse.eval nodeValue4059 x + 0)))

def numericRow2127 : Integer.Sparse Master := [(Sum.inr 1515, 2), (Sum.inr 1519, 2), (Sum.inr 1536, 2), (Sum.inr 4059, -1)]

theorem reindexCheck2127 : Integer.Sparse.reindex keyMap MixedData.row2127 = numericRow2127 := by decide +kernel

theorem numericCheck2127 (x : Master → ℝ) : Integer.Sparse.eval numericRow2127 x =
    (1 : ℝ) * reducedSource2127 x := by
  norm_num [numericRow2127, reducedSource2127, Integer.Sparse.eval, Sparse.eval, nodeValue1515, nodeValue1519, nodeValue1536, nodeValue4059]

end MUB6.Certificate.MixedSourceBridge

end OAI
