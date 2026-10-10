import OAI.Analysis.MutuallyUnbiased.MixedData.Source11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1520 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue598 x + ((1 : ℝ) * Sparse.eval nodeValue918 x + ((1 : ℝ) * Sparse.eval nodeValue1078 x + ((3 : ℝ) * Sparse.eval nodeValue1080 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow1520 : Integer.Sparse Master := [(Sum.inr 598, 1), (Sum.inr 1078, 1), (Sum.inr 1080, 3), (Sum.inr 4085, -1)]

theorem reindexCheck1520 : Integer.Sparse.reindex keyMap MixedData.row1520 = numericRow1520 := by decide +kernel

theorem numericCheck1520 (x : Master → ℝ) : Integer.Sparse.eval numericRow1520 x =
    (1 : ℝ) * reducedSource1520 x := by
  norm_num [numericRow1520, reducedSource1520, Integer.Sparse.eval, Sparse.eval, nodeValue598, nodeValue918, nodeValue1078, nodeValue1080, nodeValue4085]

noncomputable def reducedSource1521 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1252 x + ((1 : ℝ) * Sparse.eval nodeValue1255 x + ((2 : ℝ) * Sparse.eval nodeValue1270 x + ((2 : ℝ) * Sparse.eval nodeValue1272 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((2 : ℝ) * Sparse.eval nodeValue1306 x + ((2 : ℝ) * Sparse.eval nodeValue1398 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((4 : ℝ) * Sparse.eval nodeValue1415 x + ((4 : ℝ) * Sparse.eval nodeValue1427 x + ((2 : ℝ) * Sparse.eval nodeValue1448 x + ((2 : ℝ) * Sparse.eval nodeValue1449 x + ((2 : ℝ) * Sparse.eval nodeValue1478 x + ((2 : ℝ) * Sparse.eval nodeValue1484 x + 0)))))))))))))

def numericRow1521 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 5, 200), (Sum.inl 6, -60), (Sum.inl 2, 80), (Sum.inl 35, -160), (Sum.inl 1, -50), (Sum.inr 1252, 2160), (Sum.inr 1270, 2160), (Sum.inr 1272, 2160), (Sum.inr 1306, 2160), (Sum.inr 1415, 4320)]

theorem reindexCheck1521 : Integer.Sparse.reindex keyMap MixedData.row1521 = numericRow1521 := by decide +kernel

theorem numericCheck1521 (x : Master → ℝ) : Integer.Sparse.eval numericRow1521 x =
    (1080 : ℝ) * reducedSource1521 x := by
  norm_num [numericRow1521, reducedSource1521, Integer.Sparse.eval, Sparse.eval, nodeValue1252, nodeValue1255, nodeValue1270, nodeValue1272, nodeValue1305, nodeValue1306, nodeValue1398, nodeValue1414, nodeValue1415, nodeValue1427, nodeValue1448, nodeValue1449, nodeValue1478, nodeValue1484]
  ring

noncomputable def reducedSource1522 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1006 x + ((1 : ℝ) * Sparse.eval nodeValue1948 x + ((1 : ℝ) * Sparse.eval nodeValue2001 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2221 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1522 : Integer.Sparse Master := [(Sum.inr 1006, 1), (Sum.inr 1948, 1), (Sum.inr 2001, 1), (Sum.inr 2207, 1), (Sum.inr 2221, 1), (Sum.inr 2224, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1522 : Integer.Sparse.reindex keyMap MixedData.row1522 = numericRow1522 := by decide +kernel

theorem numericCheck1522 (x : Master → ℝ) : Integer.Sparse.eval numericRow1522 x =
    (1 : ℝ) * reducedSource1522 x := by
  norm_num [numericRow1522, reducedSource1522, Integer.Sparse.eval, Sparse.eval, nodeValue1006, nodeValue1948, nodeValue2001, nodeValue2207, nodeValue2221, nodeValue2224, nodeValue4081]

noncomputable def reducedSource1523 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1001 x + ((1 : ℝ) * Sparse.eval nodeValue1946 x + ((1 : ℝ) * Sparse.eval nodeValue1998 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1523 : Integer.Sparse Master := [(Sum.inr 1001, 1), (Sum.inr 1946, 1), (Sum.inr 1998, 1), (Sum.inr 2220, 1), (Sum.inr 2224, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1523 : Integer.Sparse.reindex keyMap MixedData.row1523 = numericRow1523 := by decide +kernel

theorem numericCheck1523 (x : Master → ℝ) : Integer.Sparse.eval numericRow1523 x =
    (1 : ℝ) * reducedSource1523 x := by
  norm_num [numericRow1523, reducedSource1523, Integer.Sparse.eval, Sparse.eval, nodeValue1001, nodeValue1946, nodeValue1998, nodeValue2220, nodeValue2224, nodeValue2230, nodeValue4081]

noncomputable def reducedSource1524 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1008 x + ((1 : ℝ) * Sparse.eval nodeValue1949 x + ((1 : ℝ) * Sparse.eval nodeValue2002 x + ((2 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1524 : Integer.Sparse Master := [(Sum.inr 1008, 1), (Sum.inr 1949, 1), (Sum.inr 2002, 1), (Sum.inr 2217, 2), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1524 : Integer.Sparse.reindex keyMap MixedData.row1524 = numericRow1524 := by decide +kernel

theorem numericCheck1524 (x : Master → ℝ) : Integer.Sparse.eval numericRow1524 x =
    (1 : ℝ) * reducedSource1524 x := by
  norm_num [numericRow1524, reducedSource1524, Integer.Sparse.eval, Sparse.eval, nodeValue1008, nodeValue1949, nodeValue2002, nodeValue2217, nodeValue2225, nodeValue4082]

noncomputable def reducedSource1525 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue996 x + ((2 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1008 x + ((1 : ℝ) * Sparse.eval nodeValue1071 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1525 : Integer.Sparse Master := [(Sum.inr 1000, 2), (Sum.inr 1008, 1), (Sum.inr 1071, 1), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1525 : Integer.Sparse.reindex keyMap MixedData.row1525 = numericRow1525 := by decide +kernel

theorem numericCheck1525 (x : Master → ℝ) : Integer.Sparse.eval numericRow1525 x =
    (1 : ℝ) * reducedSource1525 x := by
  norm_num [numericRow1525, reducedSource1525, Integer.Sparse.eval, Sparse.eval, nodeValue996, nodeValue1000, nodeValue1008, nodeValue1071, nodeValue2225, nodeValue4082]

noncomputable def reducedSource1526 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1947 x + ((1 : ℝ) * Sparse.eval nodeValue2000 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1526 : Integer.Sparse Master := [(Sum.inr 1005, 1), (Sum.inr 2000, 1), (Sum.inr 2206, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1526 : Integer.Sparse.reindex keyMap MixedData.row1526 = numericRow1526 := by decide +kernel

theorem numericCheck1526 (x : Master → ℝ) : Integer.Sparse.eval numericRow1526 x =
    (1 : ℝ) * reducedSource1526 x := by
  norm_num [numericRow1526, reducedSource1526, Integer.Sparse.eval, Sparse.eval, nodeValue1005, nodeValue1947, nodeValue2000, nodeValue2206, nodeValue2216, nodeValue2227, nodeValue4080]

noncomputable def reducedSource1527 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1004 x + ((2 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1527 : Integer.Sparse Master := [(Sum.inr 998, 1), (Sum.inr 1005, 2), (Sum.inr 1073, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1527 : Integer.Sparse.reindex keyMap MixedData.row1527 = numericRow1527 := by decide +kernel

theorem numericCheck1527 (x : Master → ℝ) : Integer.Sparse.eval numericRow1527 x =
    (1 : ℝ) * reducedSource1527 x := by
  norm_num [numericRow1527, reducedSource1527, Integer.Sparse.eval, Sparse.eval, nodeValue998, nodeValue1004, nodeValue1005, nodeValue1073, nodeValue2227, nodeValue4080]

noncomputable def reducedSource1528 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1945 x + ((1 : ℝ) * Sparse.eval nodeValue1997 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1528 : Integer.Sparse Master := [(Sum.inr 1000, 1), (Sum.inr 1997, 1), (Sum.inr 2215, 1), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1528 : Integer.Sparse.reindex keyMap MixedData.row1528 = numericRow1528 := by decide +kernel

theorem numericCheck1528 (x : Master → ℝ) : Integer.Sparse.eval numericRow1528 x =
    (1 : ℝ) * reducedSource1528 x := by
  norm_num [numericRow1528, reducedSource1528, Integer.Sparse.eval, Sparse.eval, nodeValue1000, nodeValue1945, nodeValue1997, nodeValue2215, nodeValue2225, nodeValue2229, nodeValue4082]

noncomputable def reducedSource1529 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue876 x + ((1 : ℝ) * Sparse.eval nodeValue881 x + ((1 : ℝ) * Sparse.eval nodeValue883 x + ((1 : ℝ) * Sparse.eval nodeValue891 x + ((1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1945 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1529 : Integer.Sparse Master := [(Sum.inr 876, 1), (Sum.inr 881, 1), (Sum.inr 891, 1), (Sum.inr 1000, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1529 : Integer.Sparse.reindex keyMap MixedData.row1529 = numericRow1529 := by decide +kernel

theorem numericCheck1529 (x : Master → ℝ) : Integer.Sparse.eval numericRow1529 x =
    (1 : ℝ) * reducedSource1529 x := by
  norm_num [numericRow1529, reducedSource1529, Integer.Sparse.eval, Sparse.eval, nodeValue876, nodeValue881, nodeValue883, nodeValue891, nodeValue1000, nodeValue1945, nodeValue4082]

noncomputable def reducedSource1530 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue999 x + ((1 : ℝ) * Sparse.eval nodeValue1944 x + ((1 : ℝ) * Sparse.eval nodeValue1996 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1530 : Integer.Sparse Master := [(Sum.inr 999, 1), (Sum.inr 1996, 1), (Sum.inr 2203, 1), (Sum.inr 2224, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1530 : Integer.Sparse.reindex keyMap MixedData.row1530 = numericRow1530 := by decide +kernel

theorem numericCheck1530 (x : Master → ℝ) : Integer.Sparse.eval numericRow1530 x =
    (1 : ℝ) * reducedSource1530 x := by
  norm_num [numericRow1530, reducedSource1530, Integer.Sparse.eval, Sparse.eval, nodeValue999, nodeValue1944, nodeValue1996, nodeValue2203, nodeValue2224, nodeValue2228, nodeValue4081]

noncomputable def reducedSource1531 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue786 x + ((2 : ℝ) * Sparse.eval nodeValue1638 x + ((2 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1531 : Integer.Sparse Master := [(Sum.inr 786, 1), (Sum.inr 1638, 2), (Sum.inr 1699, 2), (Sum.inr 1706, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1531 : Integer.Sparse.reindex keyMap MixedData.row1531 = numericRow1531 := by decide +kernel

theorem numericCheck1531 (x : Master → ℝ) : Integer.Sparse.eval numericRow1531 x =
    (1 : ℝ) * reducedSource1531 x := by
  norm_num [numericRow1531, reducedSource1531, Integer.Sparse.eval, Sparse.eval, nodeValue786, nodeValue1638, nodeValue1699, nodeValue1706, nodeValue4068]

noncomputable def reducedSource1532 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue786 x + ((2 : ℝ) * Sparse.eval nodeValue805 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1532 : Integer.Sparse Master := [(Sum.inr 783, 2), (Sum.inr 786, 1), (Sum.inr 1706, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1532 : Integer.Sparse.reindex keyMap MixedData.row1532 = numericRow1532 := by decide +kernel

theorem numericCheck1532 (x : Master → ℝ) : Integer.Sparse.eval numericRow1532 x =
    (1 : ℝ) * reducedSource1532 x := by
  norm_num [numericRow1532, reducedSource1532, Integer.Sparse.eval, Sparse.eval, nodeValue783, nodeValue786, nodeValue805, nodeValue1706, nodeValue4068]

noncomputable def reducedSource1533 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue550 x + ((2 : ℝ) * Sparse.eval nodeValue803 x + ((1 : ℝ) * Sparse.eval nodeValue822 x + ((2 : ℝ) * Sparse.eval nodeValue850 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1533 : Integer.Sparse Master := [(Sum.inr 550, 1), (Sum.inr 803, 2), (Sum.inr 822, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1533 : Integer.Sparse.reindex keyMap MixedData.row1533 = numericRow1533 := by decide +kernel

theorem numericCheck1533 (x : Master → ℝ) : Integer.Sparse.eval numericRow1533 x =
    (1 : ℝ) * reducedSource1533 x := by
  norm_num [numericRow1533, reducedSource1533, Integer.Sparse.eval, Sparse.eval, nodeValue550, nodeValue803, nodeValue822, nodeValue850, nodeValue4069]

noncomputable def reducedSource1534 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue783 x + ((2 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1534 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 1636, 2), (Sum.inr 1706, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1534 : Integer.Sparse.reindex keyMap MixedData.row1534 = numericRow1534 := by decide +kernel

theorem numericCheck1534 (x : Master → ℝ) : Integer.Sparse.eval numericRow1534 x =
    (1 : ℝ) * reducedSource1534 x := by
  norm_num [numericRow1534, reducedSource1534, Integer.Sparse.eval, Sparse.eval, nodeValue783, nodeValue1636, nodeValue1698, nodeValue1706, nodeValue1708, nodeValue4068]

noncomputable def reducedSource1535 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue537 x + ((1 : ℝ) * Sparse.eval nodeValue732 x + ((2 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue805 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1535 : Integer.Sparse Master := [(Sum.inr 537, 1), (Sum.inr 732, 1), (Sum.inr 783, 2), (Sum.inr 4068, -1)]

theorem reindexCheck1535 : Integer.Sparse.reindex keyMap MixedData.row1535 = numericRow1535 := by decide +kernel

theorem numericCheck1535 (x : Master → ℝ) : Integer.Sparse.eval numericRow1535 x =
    (1 : ℝ) * reducedSource1535 x := by
  norm_num [numericRow1535, reducedSource1535, Integer.Sparse.eval, Sparse.eval, nodeValue537, nodeValue732, nodeValue783, nodeValue805, nodeValue810, nodeValue4068]

end MUB6.Certificate.MixedSourceBridge

end OAI
