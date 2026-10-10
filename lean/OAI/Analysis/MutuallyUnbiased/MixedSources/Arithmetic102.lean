import OAI.Analysis.MutuallyUnbiased.MixedData.Source12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1632 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1337 x + ((1 : ℝ) * Sparse.eval nodeValue2437 x + ((1 : ℝ) * Sparse.eval nodeValue2442 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1632 : Integer.Sparse Master := [(Sum.inr 1337, 1), (Sum.inr 2437, 1), (Sum.inr 2442, 1), (Sum.inr 2485, 1), (Sum.inr 2618, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1632 : Integer.Sparse.reindex keyMap MixedData.row1632 = numericRow1632 := by decide +kernel

theorem numericCheck1632 (x : Master → ℝ) : Integer.Sparse.eval numericRow1632 x =
    (1 : ℝ) * reducedSource1632 x := by
  norm_num [numericRow1632, reducedSource1632, Integer.Sparse.eval, Sparse.eval, nodeValue1337, nodeValue2437, nodeValue2442, nodeValue2485, nodeValue2618, nodeValue2954, nodeValue4091]

noncomputable def reducedSource1633 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2047 x + ((1 : ℝ) * Sparse.eval nodeValue3385 x + ((1 : ℝ) * Sparse.eval nodeValue3443 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1633 : Integer.Sparse Master := [(Sum.inr 2047, 1), (Sum.inr 3385, 1), (Sum.inr 3443, 1), (Sum.inr 3468, 1), (Sum.inr 3523, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1633 : Integer.Sparse.reindex keyMap MixedData.row1633 = numericRow1633 := by decide +kernel

theorem numericCheck1633 (x : Master → ℝ) : Integer.Sparse.eval numericRow1633 x =
    (1 : ℝ) * reducedSource1633 x := by
  norm_num [numericRow1633, reducedSource1633, Integer.Sparse.eval, Sparse.eval, nodeValue2047, nodeValue3385, nodeValue3443, nodeValue3468, nodeValue3523, nodeValue3530, nodeValue4081]

noncomputable def reducedSource1634 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1998 x + ((1 : ℝ) * Sparse.eval nodeValue2004 x + ((1 : ℝ) * Sparse.eval nodeValue2006 x + ((1 : ℝ) * Sparse.eval nodeValue2049 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1634 : Integer.Sparse Master := [(Sum.inr 1998, 1), (Sum.inr 2004, 1), (Sum.inr 2006, 1), (Sum.inr 2049, 1), (Sum.inr 2230, 1), (Sum.inr 3523, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1634 : Integer.Sparse.reindex keyMap MixedData.row1634 = numericRow1634 := by decide +kernel

theorem numericCheck1634 (x : Master → ℝ) : Integer.Sparse.eval numericRow1634 x =
    (1 : ℝ) * reducedSource1634 x := by
  norm_num [numericRow1634, reducedSource1634, Integer.Sparse.eval, Sparse.eval, nodeValue1998, nodeValue2004, nodeValue2006, nodeValue2049, nodeValue2230, nodeValue3523, nodeValue4081]

noncomputable def reducedSource1635 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3615 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))

def numericRow1635 : Integer.Sparse Master := [(Sum.inr 3468, 2), (Sum.inr 3519, 1), (Sum.inr 3523, 2), (Sum.inr 3615, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1635 : Integer.Sparse.reindex keyMap MixedData.row1635 = numericRow1635 := by decide +kernel

theorem numericCheck1635 (x : Master → ℝ) : Integer.Sparse.eval numericRow1635 x =
    (1 : ℝ) * reducedSource1635 x := by
  norm_num [numericRow1635, reducedSource1635, Integer.Sparse.eval, Sparse.eval, nodeValue3468, nodeValue3519, nodeValue3523, nodeValue3615, nodeValue4081]

noncomputable def reducedSource1636 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2006 x + ((1 : ℝ) * Sparse.eval nodeValue3339 x + ((1 : ℝ) * Sparse.eval nodeValue3343 x + ((1 : ℝ) * Sparse.eval nodeValue3353 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1636 : Integer.Sparse Master := [(Sum.inr 2006, 1), (Sum.inr 3343, 1), (Sum.inr 3353, 1), (Sum.inr 3468, 1), (Sum.inr 3523, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1636 : Integer.Sparse.reindex keyMap MixedData.row1636 = numericRow1636 := by decide +kernel

theorem numericCheck1636 (x : Master → ℝ) : Integer.Sparse.eval numericRow1636 x =
    (1 : ℝ) * reducedSource1636 x := by
  norm_num [numericRow1636, reducedSource1636, Integer.Sparse.eval, Sparse.eval, nodeValue2006, nodeValue3339, nodeValue3343, nodeValue3353, nodeValue3468, nodeValue3523, nodeValue4081]

noncomputable def reducedSource1637 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2118 x + ((1 : ℝ) * Sparse.eval nodeValue2121 x + ((1 : ℝ) * Sparse.eval nodeValue2123 x + ((1 : ℝ) * Sparse.eval nodeValue2129 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1637 : Integer.Sparse Master := [(Sum.inr 2118, 1), (Sum.inr 2121, 1), (Sum.inr 2123, 1), (Sum.inr 2129, 1), (Sum.inr 2216, 1), (Sum.inr 2735, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1637 : Integer.Sparse.reindex keyMap MixedData.row1637 = numericRow1637 := by decide +kernel

theorem numericCheck1637 (x : Master → ℝ) : Integer.Sparse.eval numericRow1637 x =
    (1 : ℝ) * reducedSource1637 x := by
  norm_num [numericRow1637, reducedSource1637, Integer.Sparse.eval, Sparse.eval, nodeValue2118, nodeValue2121, nodeValue2123, nodeValue2129, nodeValue2216, nodeValue2735, nodeValue4080]

noncomputable def reducedSource1638 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2425 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2542 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1638 : Integer.Sparse Master := [(Sum.inr 1148, 1), (Sum.inr 2347, 1), (Sum.inr 2425, 1), (Sum.inr 2482, 1), (Sum.inr 2553, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1638 : Integer.Sparse.reindex keyMap MixedData.row1638 = numericRow1638 := by decide +kernel

theorem numericCheck1638 (x : Master → ℝ) : Integer.Sparse.eval numericRow1638 x =
    (1 : ℝ) * reducedSource1638 x := by
  norm_num [numericRow1638, reducedSource1638, Integer.Sparse.eval, Sparse.eval, nodeValue1148, nodeValue2347, nodeValue2425, nodeValue2482, nodeValue2542, nodeValue2553, nodeValue4092]

noncomputable def reducedSource1639 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3432 x + ((1 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1639 : Integer.Sparse Master := [(Sum.inr 3432, 1), (Sum.inr 3434, 1), (Sum.inr 3437, 1), (Sum.inr 3481, 1), (Sum.inr 3519, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1639 : Integer.Sparse.reindex keyMap MixedData.row1639 = numericRow1639 := by decide +kernel

theorem numericCheck1639 (x : Master → ℝ) : Integer.Sparse.eval numericRow1639 x =
    (1 : ℝ) * reducedSource1639 x := by
  norm_num [numericRow1639, reducedSource1639, Integer.Sparse.eval, Sparse.eval, nodeValue3432, nodeValue3434, nodeValue3437, nodeValue3481, nodeValue3513, nodeValue3519, nodeValue4081]

noncomputable def reducedSource1640 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1986 x + ((1 : ℝ) * Sparse.eval nodeValue1989 x + ((1 : ℝ) * Sparse.eval nodeValue1996 x + ((1 : ℝ) * Sparse.eval nodeValue2015 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1640 : Integer.Sparse Master := [(Sum.inr 1986, 1), (Sum.inr 1989, 1), (Sum.inr 1996, 1), (Sum.inr 2015, 1), (Sum.inr 2203, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1640 : Integer.Sparse.reindex keyMap MixedData.row1640 = numericRow1640 := by decide +kernel

theorem numericCheck1640 (x : Master → ℝ) : Integer.Sparse.eval numericRow1640 x =
    (1 : ℝ) * reducedSource1640 x := by
  norm_num [numericRow1640, reducedSource1640, Integer.Sparse.eval, Sparse.eval, nodeValue1986, nodeValue1989, nodeValue1996, nodeValue2015, nodeValue2203, nodeValue3513, nodeValue4081]

noncomputable def reducedSource1641 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1996 x + ((1 : ℝ) * Sparse.eval nodeValue3368 x + ((1 : ℝ) * Sparse.eval nodeValue3432 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1641 : Integer.Sparse Master := [(Sum.inr 1996, 1), (Sum.inr 3368, 1), (Sum.inr 3432, 1), (Sum.inr 3468, 1), (Sum.inr 3519, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1641 : Integer.Sparse.reindex keyMap MixedData.row1641 = numericRow1641 := by decide +kernel

theorem numericCheck1641 (x : Master → ℝ) : Integer.Sparse.eval numericRow1641 x =
    (1 : ℝ) * reducedSource1641 x := by
  norm_num [numericRow1641, reducedSource1641, Integer.Sparse.eval, Sparse.eval, nodeValue1996, nodeValue3368, nodeValue3432, nodeValue3468, nodeValue3513, nodeValue3519, nodeValue4081]

noncomputable def reducedSource1642 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3608 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1642 : Integer.Sparse Master := [(Sum.inr 2203, 1), (Sum.inr 3468, 1), (Sum.inr 3481, 1), (Sum.inr 3530, 1), (Sum.inr 3608, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1642 : Integer.Sparse.reindex keyMap MixedData.row1642 = numericRow1642 := by decide +kernel

theorem numericCheck1642 (x : Master → ℝ) : Integer.Sparse.eval numericRow1642 x =
    (1 : ℝ) * reducedSource1642 x := by
  norm_num [numericRow1642, reducedSource1642, Integer.Sparse.eval, Sparse.eval, nodeValue2203, nodeValue3468, nodeValue3481, nodeValue3513, nodeValue3530, nodeValue3608, nodeValue4081]

noncomputable def reducedSource1643 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1643 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 2422, 1), (Sum.inr 2429, 1), (Sum.inr 2485, 1), (Sum.inr 2543, 1), (Sum.inr 2924, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1643 : Integer.Sparse.reindex keyMap MixedData.row1643 = numericRow1643 := by decide +kernel

theorem numericCheck1643 (x : Master → ℝ) : Integer.Sparse.eval numericRow1643 x =
    (1 : ℝ) * reducedSource1643 x := by
  norm_num [numericRow1643, reducedSource1643, Integer.Sparse.eval, Sparse.eval, nodeValue1327, nodeValue2422, nodeValue2429, nodeValue2485, nodeValue2543, nodeValue2924, nodeValue4091]

noncomputable def reducedSource1644 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1150 x + ((1 : ℝ) * Sparse.eval nodeValue2349 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((2 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1644 : Integer.Sparse Master := [(Sum.inr 1150, 1), (Sum.inr 2349, 1), (Sum.inr 2429, 1), (Sum.inr 2543, 2), (Sum.inr 2556, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1644 : Integer.Sparse.reindex keyMap MixedData.row1644 = numericRow1644 := by decide +kernel

theorem numericCheck1644 (x : Master → ℝ) : Integer.Sparse.eval numericRow1644 x =
    (1 : ℝ) * reducedSource1644 x := by
  norm_num [numericRow1644, reducedSource1644, Integer.Sparse.eval, Sparse.eval, nodeValue1150, nodeValue2349, nodeValue2429, nodeValue2543, nodeValue2556, nodeValue4091]

noncomputable def reducedSource1645 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2071 x + ((1 : ℝ) * Sparse.eval nodeValue2073 x + ((1 : ℝ) * Sparse.eval nodeValue2077 x + ((1 : ℝ) * Sparse.eval nodeValue2086 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))))

def numericRow1645 : Integer.Sparse Master := [(Sum.inr 2071, 1), (Sum.inr 2073, 1), (Sum.inr 2077, 1), (Sum.inr 2086, 1), (Sum.inr 2191, 1), (Sum.inr 3558, 1), (Sum.inr 4079, -1)]

theorem reindexCheck1645 : Integer.Sparse.reindex keyMap MixedData.row1645 = numericRow1645 := by decide +kernel

theorem numericCheck1645 (x : Master → ℝ) : Integer.Sparse.eval numericRow1645 x =
    (1 : ℝ) * reducedSource1645 x := by
  norm_num [numericRow1645, reducedSource1645, Integer.Sparse.eval, Sparse.eval, nodeValue2071, nodeValue2073, nodeValue2077, nodeValue2086, nodeValue2191, nodeValue3558, nodeValue4079]

noncomputable def reducedSource1646 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2454 x + ((1 : ℝ) * Sparse.eval nodeValue2456 x + ((1 : ℝ) * Sparse.eval nodeValue2462 x + ((1 : ℝ) * Sparse.eval nodeValue2491 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))))

def numericRow1646 : Integer.Sparse Master := [(Sum.inr 2454, 1), (Sum.inr 2456, 1), (Sum.inr 2462, 1), (Sum.inr 2491, 1), (Sum.inr 2698, 1), (Sum.inr 3796, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1646 : Integer.Sparse.reindex keyMap MixedData.row1646 = numericRow1646 := by decide +kernel

theorem numericCheck1646 (x : Master → ℝ) : Integer.Sparse.eval numericRow1646 x =
    (1 : ℝ) * reducedSource1646 x := by
  norm_num [numericRow1646, reducedSource1646, Integer.Sparse.eval, Sparse.eval, nodeValue2454, nodeValue2456, nodeValue2462, nodeValue2491, nodeValue2698, nodeValue3796, nodeValue4090]

noncomputable def reducedSource1647 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1992 x + ((1 : ℝ) * Sparse.eval nodeValue1994 x + ((1 : ℝ) * Sparse.eval nodeValue2000 x + ((1 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1647 : Integer.Sparse Master := [(Sum.inr 1992, 1), (Sum.inr 1994, 1), (Sum.inr 2000, 1), (Sum.inr 2031, 1), (Sum.inr 2216, 1), (Sum.inr 3517, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1647 : Integer.Sparse.reindex keyMap MixedData.row1647 = numericRow1647 := by decide +kernel

theorem numericCheck1647 (x : Master → ℝ) : Integer.Sparse.eval numericRow1647 x =
    (1 : ℝ) * reducedSource1647 x := by
  norm_num [numericRow1647, reducedSource1647, Integer.Sparse.eval, Sparse.eval, nodeValue1992, nodeValue1994, nodeValue2000, nodeValue2031, nodeValue2216, nodeValue3517, nodeValue4080]

end MUB6.Certificate.MixedSourceBridge

end OAI
