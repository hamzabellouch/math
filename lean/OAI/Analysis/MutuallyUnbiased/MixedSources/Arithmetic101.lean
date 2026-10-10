import OAI.Analysis.MutuallyUnbiased.MixedData.Source12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1616 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1903 x + ((1 : ℝ) * Sparse.eval nodeValue1904 x + ((1 : ℝ) * Sparse.eval nodeValue1913 x + ((1 : ℝ) * Sparse.eval nodeValue1925 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1616 : Integer.Sparse Master := [(Sum.inr 1903, 1), (Sum.inr 1904, 1), (Sum.inr 1913, 1), (Sum.inr 1925, 1), (Sum.inr 2196, 1), (Sum.inr 3464, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1616 : Integer.Sparse.reindex keyMap MixedData.row1616 = numericRow1616 := by decide +kernel

theorem numericCheck1616 (x : Master → ℝ) : Integer.Sparse.eval numericRow1616 x =
    (1 : ℝ) * reducedSource1616 x := by
  norm_num [numericRow1616, reducedSource1616, Integer.Sparse.eval, Sparse.eval, nodeValue1903, nodeValue1904, nodeValue1913, nodeValue1925, nodeValue2196, nodeValue3464, nodeValue4080]

noncomputable def reducedSource1617 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue954 x + ((1 : ℝ) * Sparse.eval nodeValue1832 x + ((2 : ℝ) * Sparse.eval nodeValue1980 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1617 : Integer.Sparse Master := [(Sum.inr 954, 1), (Sum.inr 1832, 1), (Sum.inr 1980, 2), (Sum.inr 2113, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1617 : Integer.Sparse.reindex keyMap MixedData.row1617 = numericRow1617 := by decide +kernel

theorem numericCheck1617 (x : Master → ℝ) : Integer.Sparse.eval numericRow1617 x =
    (1 : ℝ) * reducedSource1617 x := by
  norm_num [numericRow1617, reducedSource1617, Integer.Sparse.eval, Sparse.eval, nodeValue954, nodeValue1832, nodeValue1980, nodeValue2113, nodeValue2115, nodeValue4084]

noncomputable def reducedSource1618 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue945 x + ((1 : ℝ) * Sparse.eval nodeValue1825 x + ((1 : ℝ) * Sparse.eval nodeValue1973 x + ((1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1618 : Integer.Sparse Master := [(Sum.inr 945, 1), (Sum.inr 1825, 1), (Sum.inr 1973, 1), (Sum.inr 2090, 1), (Sum.inr 2107, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1618 : Integer.Sparse.reindex keyMap MixedData.row1618 = numericRow1618 := by decide +kernel

theorem numericCheck1618 (x : Master → ℝ) : Integer.Sparse.eval numericRow1618 x =
    (1 : ℝ) * reducedSource1618 x := by
  norm_num [numericRow1618, reducedSource1618, Integer.Sparse.eval, Sparse.eval, nodeValue945, nodeValue1825, nodeValue1973, nodeValue2090, nodeValue2107, nodeValue2112, nodeValue4083]

noncomputable def reducedSource1619 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1121 x + ((1 : ℝ) * Sparse.eval nodeValue2327 x + ((1 : ℝ) * Sparse.eval nodeValue2423 x + ((1 : ℝ) * Sparse.eval nodeValue2443 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1619 : Integer.Sparse Master := [(Sum.inr 1121, 1), (Sum.inr 2327, 1), (Sum.inr 2423, 1), (Sum.inr 2443, 1), (Sum.inr 2486, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1619 : Integer.Sparse.reindex keyMap MixedData.row1619 = numericRow1619 := by decide +kernel

theorem numericCheck1619 (x : Master → ℝ) : Integer.Sparse.eval numericRow1619 x =
    (1 : ℝ) * reducedSource1619 x := by
  norm_num [numericRow1619, reducedSource1619, Integer.Sparse.eval, Sparse.eval, nodeValue1121, nodeValue2327, nodeValue2423, nodeValue2443, nodeValue2486, nodeValue2488, nodeValue4092]

noncomputable def reducedSource1620 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1946 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue3355 x + ((1 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1620 : Integer.Sparse Master := [(Sum.inr 1946, 1), (Sum.inr 2259, 1), (Sum.inr 3355, 1), (Sum.inr 3434, 1), (Sum.inr 3481, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1620 : Integer.Sparse.reindex keyMap MixedData.row1620 = numericRow1620 := by decide +kernel

theorem numericCheck1620 (x : Master → ℝ) : Integer.Sparse.eval numericRow1620 x =
    (1 : ℝ) * reducedSource1620 x := by
  norm_num [numericRow1620, reducedSource1620, Integer.Sparse.eval, Sparse.eval, nodeValue1946, nodeValue2259, nodeValue3355, nodeValue3434, nodeValue3481, nodeValue3486, nodeValue4081]

noncomputable def reducedSource1621 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1621 : Integer.Sparse Master := [(Sum.inr 2259, 2), (Sum.inr 2261, 1), (Sum.inr 2267, 1), (Sum.inr 2287, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1621 : Integer.Sparse.reindex keyMap MixedData.row1621 = numericRow1621 := by decide +kernel

theorem numericCheck1621 (x : Master → ℝ) : Integer.Sparse.eval numericRow1621 x =
    (1 : ℝ) * reducedSource1621 x := by
  norm_num [numericRow1621, reducedSource1621, Integer.Sparse.eval, Sparse.eval, nodeValue2259, nodeValue2261, nodeValue2267, nodeValue2287, nodeValue3486, nodeValue4081]

noncomputable def reducedSource1622 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1923 x + ((1 : ℝ) * Sparse.eval nodeValue1927 x + ((1 : ℝ) * Sparse.eval nodeValue1928 x + ((1 : ℝ) * Sparse.eval nodeValue1949 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1622 : Integer.Sparse Master := [(Sum.inr 1923, 1), (Sum.inr 1927, 1), (Sum.inr 1928, 1), (Sum.inr 1949, 1), (Sum.inr 2217, 1), (Sum.inr 3480, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1622 : Integer.Sparse.reindex keyMap MixedData.row1622 = numericRow1622 := by decide +kernel

theorem numericCheck1622 (x : Master → ℝ) : Integer.Sparse.eval numericRow1622 x =
    (1 : ℝ) * reducedSource1622 x := by
  norm_num [numericRow1622, reducedSource1622, Integer.Sparse.eval, Sparse.eval, nodeValue1923, nodeValue1927, nodeValue1928, nodeValue1949, nodeValue2217, nodeValue3480, nodeValue4082]

noncomputable def reducedSource1623 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1146 x + ((1 : ℝ) * Sparse.eval nodeValue2346 x + ((2 : ℝ) * Sparse.eval nodeValue2435 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1623 : Integer.Sparse Master := [(Sum.inr 1146, 1), (Sum.inr 2346, 1), (Sum.inr 2435, 2), (Sum.inr 2520, 1), (Sum.inr 2522, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1623 : Integer.Sparse.reindex keyMap MixedData.row1623 = numericRow1623 := by decide +kernel

theorem numericCheck1623 (x : Master → ℝ) : Integer.Sparse.eval numericRow1623 x =
    (1 : ℝ) * reducedSource1623 x := by
  norm_num [numericRow1623, reducedSource1623, Integer.Sparse.eval, Sparse.eval, nodeValue1146, nodeValue2346, nodeValue2435, nodeValue2520, nodeValue2522, nodeValue4084]

noncomputable def reducedSource1624 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1951 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((2 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1624 : Integer.Sparse Master := [(Sum.inr 1951, 1), (Sum.inr 2267, 1), (Sum.inr 2837, 2), (Sum.inr 2842, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1624 : Integer.Sparse.reindex keyMap MixedData.row1624 = numericRow1624 := by decide +kernel

theorem numericCheck1624 (x : Master → ℝ) : Integer.Sparse.eval numericRow1624 x =
    (1 : ℝ) * reducedSource1624 x := by
  norm_num [numericRow1624, reducedSource1624, Integer.Sparse.eval, Sparse.eval, nodeValue1951, nodeValue2267, nodeValue2837, nodeValue2842, nodeValue3486, nodeValue4081]

noncomputable def reducedSource1625 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1132 x + ((1 : ℝ) * Sparse.eval nodeValue2335 x + ((1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1625 : Integer.Sparse Master := [(Sum.inr 1132, 1), (Sum.inr 2335, 1), (Sum.inr 2426, 1), (Sum.inr 2495, 1), (Sum.inr 2512, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1625 : Integer.Sparse.reindex keyMap MixedData.row1625 = numericRow1625 := by decide +kernel

theorem numericCheck1625 (x : Master → ℝ) : Integer.Sparse.eval numericRow1625 x =
    (1 : ℝ) * reducedSource1625 x := by
  norm_num [numericRow1625, reducedSource1625, Integer.Sparse.eval, Sparse.eval, nodeValue1132, nodeValue2335, nodeValue2426, nodeValue2495, nodeValue2512, nodeValue2519, nodeValue4092]

noncomputable def reducedSource1626 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1917 x + ((1 : ℝ) * Sparse.eval nodeValue3343 x + ((1 : ℝ) * Sparse.eval nodeValue3368 x + ((1 : ℝ) * Sparse.eval nodeValue3385 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1626 : Integer.Sparse Master := [(Sum.inr 1917, 1), (Sum.inr 3343, 1), (Sum.inr 3368, 1), (Sum.inr 3385, 1), (Sum.inr 3468, 1), (Sum.inr 3472, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1626 : Integer.Sparse.reindex keyMap MixedData.row1626 = numericRow1626 := by decide +kernel

theorem numericCheck1626 (x : Master → ℝ) : Integer.Sparse.eval numericRow1626 x =
    (1 : ℝ) * reducedSource1626 x := by
  norm_num [numericRow1626, reducedSource1626, Integer.Sparse.eval, Sparse.eval, nodeValue1917, nodeValue3343, nodeValue3368, nodeValue3385, nodeValue3468, nodeValue3472, nodeValue4081]

noncomputable def reducedSource1627 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))

def numericRow1627 : Integer.Sparse Master := [(Sum.inr 3466, 1), (Sum.inr 3468, 2), (Sum.inr 3472, 1), (Sum.inr 3481, 2), (Sum.inr 4081, -1)]

theorem reindexCheck1627 : Integer.Sparse.reindex keyMap MixedData.row1627 = numericRow1627 := by decide +kernel

theorem numericCheck1627 (x : Master → ℝ) : Integer.Sparse.eval numericRow1627 x =
    (1 : ℝ) * reducedSource1627 x := by
  norm_num [numericRow1627, reducedSource1627, Integer.Sparse.eval, Sparse.eval, nodeValue3466, nodeValue3468, nodeValue3472, nodeValue3481, nodeValue4081]

noncomputable def reducedSource1628 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1112 x + ((1 : ℝ) * Sparse.eval nodeValue2320 x + ((1 : ℝ) * Sparse.eval nodeValue2437 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1628 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 2320, 1), (Sum.inr 2437, 1), (Sum.inr 2470, 1), (Sum.inr 2480, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1628 : Integer.Sparse.reindex keyMap MixedData.row1628 = numericRow1628 := by decide +kernel

theorem numericCheck1628 (x : Master → ℝ) : Integer.Sparse.eval numericRow1628 x =
    (1 : ℝ) * reducedSource1628 x := by
  norm_num [numericRow1628, reducedSource1628, Integer.Sparse.eval, Sparse.eval, nodeValue1112, nodeValue2320, nodeValue2437, nodeValue2470, nodeValue2480, nodeValue2485, nodeValue4091]

noncomputable def reducedSource1629 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1907 x + ((1 : ℝ) * Sparse.eval nodeValue3339 x + ((1 : ℝ) * Sparse.eval nodeValue3443 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3468 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1629 : Integer.Sparse Master := [(Sum.inr 1907, 1), (Sum.inr 3443, 1), (Sum.inr 3466, 1), (Sum.inr 3468, 2), (Sum.inr 4081, -1)]

theorem reindexCheck1629 : Integer.Sparse.reindex keyMap MixedData.row1629 = numericRow1629 := by decide +kernel

theorem numericCheck1629 (x : Master → ℝ) : Integer.Sparse.eval numericRow1629 x =
    (1 : ℝ) * reducedSource1629 x := by
  norm_num [numericRow1629, reducedSource1629, Integer.Sparse.eval, Sparse.eval, nodeValue1907, nodeValue3339, nodeValue3443, nodeValue3466, nodeValue3468, nodeValue4081]

noncomputable def reducedSource1630 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2434 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1630 : Integer.Sparse Master := [(Sum.inr 1317, 1), (Sum.inr 2426, 1), (Sum.inr 2434, 1), (Sum.inr 2519, 1), (Sum.inr 2558, 1), (Sum.inr 2881, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1630 : Integer.Sparse.reindex keyMap MixedData.row1630 = numericRow1630 := by decide +kernel

theorem numericCheck1630 (x : Master → ℝ) : Integer.Sparse.eval numericRow1630 x =
    (1 : ℝ) * reducedSource1630 x := by
  norm_num [numericRow1630, reducedSource1630, Integer.Sparse.eval, Sparse.eval, nodeValue1317, nodeValue2426, nodeValue2434, nodeValue2519, nodeValue2558, nodeValue2881, nodeValue4092]

noncomputable def reducedSource1631 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1155 x + ((1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2434 x + ((1 : ℝ) * Sparse.eval nodeValue2524 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1631 : Integer.Sparse Master := [(Sum.inr 1155, 1), (Sum.inr 2352, 1), (Sum.inr 2434, 1), (Sum.inr 2524, 1), (Sum.inr 2558, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1631 : Integer.Sparse.reindex keyMap MixedData.row1631 = numericRow1631 := by decide +kernel

theorem numericCheck1631 (x : Master → ℝ) : Integer.Sparse.eval numericRow1631 x =
    (1 : ℝ) * reducedSource1631 x := by
  norm_num [numericRow1631, reducedSource1631, Integer.Sparse.eval, Sparse.eval, nodeValue1155, nodeValue2352, nodeValue2434, nodeValue2524, nodeValue2558, nodeValue2561, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
