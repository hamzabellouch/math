import OAI.Analysis.MutuallyUnbiased.MixedData.Source10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1312 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1220 x + ((2 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((2 : ℝ) * Sparse.eval nodeValue1363 x + ((2 : ℝ) * Sparse.eval nodeValue1375 x + ((2 : ℝ) * Sparse.eval nodeValue1381 x + ((4 : ℝ) * Sparse.eval nodeValue1391 x + ((4 : ℝ) * Sparse.eval nodeValue1401 x + ((2 : ℝ) * Sparse.eval nodeValue1419 x + ((2 : ℝ) * Sparse.eval nodeValue1420 x + ((2 : ℝ) * Sparse.eval nodeValue1455 x + ((1 : ℝ) * Sparse.eval nodeValue1473 x + ((2 : ℝ) * Sparse.eval nodeValue1479 x + ((2 : ℝ) * Sparse.eval nodeValue1486 x + 0)))))))))))))

def numericRow1312 : Integer.Sparse Master := [(Sum.inl 0, -27), (Sum.inl 5, -130), (Sum.inl 8, -40), (Sum.inl 1, 5), (Sum.inr 1220, 540), (Sum.inr 1246, 540), (Sum.inr 1363, 540), (Sum.inr 1375, 540), (Sum.inr 1391, 1080)]

theorem reindexCheck1312 : Integer.Sparse.reindex keyMap MixedData.row1312 = numericRow1312 := by decide +kernel

theorem numericCheck1312 (x : Master → ℝ) : Integer.Sparse.eval numericRow1312 x =
    (270 : ℝ) * reducedSource1312 x := by
  norm_num [numericRow1312, reducedSource1312, Integer.Sparse.eval, Sparse.eval, nodeValue1220, nodeValue1246, nodeValue1312, nodeValue1363, nodeValue1375, nodeValue1381, nodeValue1391, nodeValue1401, nodeValue1419, nodeValue1420, nodeValue1455, nodeValue1473, nodeValue1479, nodeValue1486]
  ring

noncomputable def reducedSource1313 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue984 x + ((1 : ℝ) * Sparse.eval nodeValue1917 x + ((1 : ℝ) * Sparse.eval nodeValue1989 x + ((1 : ℝ) * Sparse.eval nodeValue2081 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1313 : Integer.Sparse Master := [(Sum.inr 984, 1), (Sum.inr 1917, 1), (Sum.inr 1989, 1), (Sum.inr 2081, 1), (Sum.inr 2203, 1), (Sum.inr 2207, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1313 : Integer.Sparse.reindex keyMap MixedData.row1313 = numericRow1313 := by decide +kernel

theorem numericCheck1313 (x : Master → ℝ) : Integer.Sparse.eval numericRow1313 x =
    (1 : ℝ) * reducedSource1313 x := by
  norm_num [numericRow1313, reducedSource1313, Integer.Sparse.eval, Sparse.eval, nodeValue984, nodeValue1917, nodeValue1989, nodeValue2081, nodeValue2203, nodeValue2207, nodeValue4081]

noncomputable def reducedSource1314 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1918 x + ((1 : ℝ) * Sparse.eval nodeValue1990 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1314 : Integer.Sparse Master := [(Sum.inr 985, 1), (Sum.inr 1990, 1), (Sum.inr 2082, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1314 : Integer.Sparse.reindex keyMap MixedData.row1314 = numericRow1314 := by decide +kernel

theorem numericCheck1314 (x : Master → ℝ) : Integer.Sparse.eval numericRow1314 x =
    (1 : ℝ) * reducedSource1314 x := by
  norm_num [numericRow1314, reducedSource1314, Integer.Sparse.eval, Sparse.eval, nodeValue985, nodeValue1918, nodeValue1990, nodeValue2082, nodeValue2205, nodeValue2206, nodeValue4080]

noncomputable def reducedSource1315 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue866 x + ((1 : ℝ) * Sparse.eval nodeValue873 x + ((1 : ℝ) * Sparse.eval nodeValue874 x + ((1 : ℝ) * Sparse.eval nodeValue889 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1918 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1315 : Integer.Sparse Master := [(Sum.inr 866, 1), (Sum.inr 873, 1), (Sum.inr 874, 1), (Sum.inr 985, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1315 : Integer.Sparse.reindex keyMap MixedData.row1315 = numericRow1315 := by decide +kernel

theorem numericCheck1315 (x : Master → ℝ) : Integer.Sparse.eval numericRow1315 x =
    (1 : ℝ) * reducedSource1315 x := by
  norm_num [numericRow1315, reducedSource1315, Integer.Sparse.eval, Sparse.eval, nodeValue866, nodeValue873, nodeValue874, nodeValue889, nodeValue985, nodeValue1918, nodeValue4080]

noncomputable def reducedSource1316 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue710 x + ((1 : ℝ) * Sparse.eval nodeValue715 x + ((1 : ℝ) * Sparse.eval nodeValue717 x + ((1 : ℝ) * Sparse.eval nodeValue724 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((1 : ℝ) * Sparse.eval nodeValue1618 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))))

def numericRow1316 : Integer.Sparse Master := [(Sum.inr 710, 1), (Sum.inr 715, 1), (Sum.inr 724, 1), (Sum.inr 1618, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1316 : Integer.Sparse.reindex keyMap MixedData.row1316 = numericRow1316 := by decide +kernel

theorem numericCheck1316 (x : Master → ℝ) : Integer.Sparse.eval numericRow1316 x =
    (1 : ℝ) * reducedSource1316 x := by
  norm_num [numericRow1316, reducedSource1316, Integer.Sparse.eval, Sparse.eval, nodeValue710, nodeValue715, nodeValue717, nodeValue724, nodeValue852, nodeValue1618, nodeValue4071]

noncomputable def reducedSource1317 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4179 x + ((1 : ℝ) * Sparse.eval nodeValue4190 x + ((1 : ℝ) * Sparse.eval nodeValue4193 x + ((6 : ℝ) * Sparse.eval nodeValue4348 x + ((3 : ℝ) * Sparse.eval nodeValue4359 x + ((3 : ℝ) * Sparse.eval nodeValue4362 x + ((3 : ℝ) * Sparse.eval nodeValue4496 x + ((3 : ℝ) * Sparse.eval nodeValue4500 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + ((1 : ℝ) * Sparse.eval nodeValue4508 x + ((3 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + 0))))))))))))

def numericRow1317 : Integer.Sparse Master := [(Sum.inr 618, -1), (Sum.inr 937, -3), (Sum.inr 1080, -3), (Sum.inr 1527, -1), (Sum.inr 1683, -3), (Sum.inr 1710, -3), (Sum.inr 2065, -3), (Sum.inr 2218, -3), (Sum.inr 2281, -1), (Sum.inr 2294, -1), (Sum.inr 4179, 12), (Sum.inr 4193, 4), (Sum.inr 4348, 24), (Sum.inr 4362, 12), (Sum.inr 4500, 12), (Sum.inr 4508, 4)]

theorem reindexCheck1317 : Integer.Sparse.reindex keyMap MixedData.row1317 = numericRow1317 := by decide +kernel

theorem numericCheck1317 (x : Master → ℝ) : Integer.Sparse.eval numericRow1317 x =
    (4 : ℝ) * reducedSource1317 x := by
  norm_num [numericRow1317, reducedSource1317, Integer.Sparse.eval, Sparse.eval, nodeValue4179, nodeValue4190, nodeValue4193, nodeValue4348, nodeValue4359, nodeValue4362, nodeValue4496, nodeValue4500, nodeValue4501, nodeValue4508, nodeValue4845, nodeValue4897, nodeValue4899]
  ring

noncomputable def reducedSource1318 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue653 x + ((1 : ℝ) * Sparse.eval nodeValue654 x + ((1 : ℝ) * Sparse.eval nodeValue655 x + ((6 : ℝ) * Sparse.eval nodeValue1347 x + ((3 : ℝ) * Sparse.eval nodeValue1348 x + ((3 : ℝ) * Sparse.eval nodeValue1349 x + ((3 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue1438 x + ((3 : ℝ) * Sparse.eval nodeValue1451 x + ((1 : ℝ) * Sparse.eval nodeValue1452 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((3 : ℝ) * Sparse.eval nodeValue3095 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + 0))))))))))))

def numericRow1318 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 5, 40), (Sum.inl 2, -200), (Sum.inl 35, 160), (Sum.inl 1, -10), (Sum.inr 653, 1440), (Sum.inr 654, 480), (Sum.inr 1347, 2880), (Sum.inr 1348, 1440), (Sum.inr 1436, 1440), (Sum.inr 1438, 480)]

theorem reindexCheck1318 : Integer.Sparse.reindex keyMap MixedData.row1318 = numericRow1318 := by decide +kernel

theorem numericCheck1318 (x : Master → ℝ) : Integer.Sparse.eval numericRow1318 x =
    (480 : ℝ) * reducedSource1318 x := by
  norm_num [numericRow1318, reducedSource1318, Integer.Sparse.eval, Sparse.eval, nodeValue653, nodeValue654, nodeValue655, nodeValue1347, nodeValue1348, nodeValue1349, nodeValue1436, nodeValue1438, nodeValue1451, nodeValue1452, nodeValue2778, nodeValue3095, nodeValue3114]
  ring

noncomputable def reducedSource1319 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1513 x + ((1 : ℝ) * Sparse.eval nodeValue1527 x + ((1 : ℝ) * Sparse.eval nodeValue1531 x + ((6 : ℝ) * Sparse.eval nodeValue1669 x + ((3 : ℝ) * Sparse.eval nodeValue1683 x + ((3 : ℝ) * Sparse.eval nodeValue1687 x + ((3 : ℝ) * Sparse.eval nodeValue1710 x + ((3 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((3 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + 0))))))))))))

def numericRow1319 : Integer.Sparse Master := [(Sum.inr 1513, 3), (Sum.inr 1527, 1), (Sum.inr 1531, 1), (Sum.inr 1669, 6), (Sum.inr 1683, 3), (Sum.inr 1687, 3), (Sum.inr 1710, 3), (Sum.inr 1716, 3), (Sum.inr 1747, 1), (Sum.inr 2218, 3), (Sum.inr 2281, 1)]

theorem reindexCheck1319 : Integer.Sparse.reindex keyMap MixedData.row1319 = numericRow1319 := by decide +kernel

theorem numericCheck1319 (x : Master → ℝ) : Integer.Sparse.eval numericRow1319 x =
    (1 : ℝ) * reducedSource1319 x := by
  norm_num [numericRow1319, reducedSource1319, Integer.Sparse.eval, Sparse.eval, nodeValue1513, nodeValue1527, nodeValue1531, nodeValue1669, nodeValue1683, nodeValue1687, nodeValue1710, nodeValue1716, nodeValue1730, nodeValue1747, nodeValue2218, nodeValue2268, nodeValue2281]

noncomputable def reducedSource1320 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue607 x + ((1 : ℝ) * Sparse.eval nodeValue618 x + ((1 : ℝ) * Sparse.eval nodeValue621 x + ((1 : ℝ) * Sparse.eval nodeValue1094 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow1320 : Integer.Sparse Master := [(Sum.inr 607, 3), (Sum.inr 618, 1), (Sum.inr 621, 1), (Sum.inr 1094, 1), (Sum.inr 4085, -1)]

theorem reindexCheck1320 : Integer.Sparse.reindex keyMap MixedData.row1320 = numericRow1320 := by decide +kernel

theorem numericCheck1320 (x : Master → ℝ) : Integer.Sparse.eval numericRow1320 x =
    (1 : ℝ) * reducedSource1320 x := by
  norm_num [numericRow1320, reducedSource1320, Integer.Sparse.eval, Sparse.eval, nodeValue607, nodeValue618, nodeValue621, nodeValue1094, nodeValue4085]

noncomputable def reducedSource1321 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((3 : ℝ) * Sparse.eval nodeValue4180 x + ((1 : ℝ) * Sparse.eval nodeValue4191 x + ((1 : ℝ) * Sparse.eval nodeValue4192 x + ((6 : ℝ) * Sparse.eval nodeValue4349 x + ((3 : ℝ) * Sparse.eval nodeValue4360 x + ((3 : ℝ) * Sparse.eval nodeValue4361 x + ((3 : ℝ) * Sparse.eval nodeValue4498 x + ((3 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((3 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + 0))))))))))))

def numericRow1321 : Integer.Sparse Master := [(Sum.inr 608, -3), (Sum.inr 619, -1), (Sum.inr 620, -1), (Sum.inr 927, -6), (Sum.inr 938, -3), (Sum.inr 939, -3), (Sum.inr 1083, -3), (Sum.inr 1091, -1), (Sum.inr 1519, -3), (Sum.inr 1538, -1), (Sum.inr 1539, -1), (Sum.inr 1675, -6), (Sum.inr 1693, -3), (Sum.inr 1694, -3), (Sum.inr 1728, -3), (Sum.inr 1756, -1), (Sum.inr 4084, 4)]

theorem reindexCheck1321 : Integer.Sparse.reindex keyMap MixedData.row1321 = numericRow1321 := by decide +kernel

theorem numericCheck1321 (x : Master → ℝ) : Integer.Sparse.eval numericRow1321 x =
    (4 : ℝ) * reducedSource1321 x := by
  norm_num [numericRow1321, reducedSource1321, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4180, nodeValue4191, nodeValue4192, nodeValue4349, nodeValue4360, nodeValue4361, nodeValue4498, nodeValue4499, nodeValue4505, nodeValue4507, nodeValue4846, nodeValue4901]
  ring

noncomputable def reducedSource1322 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1519 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((6 : ℝ) * Sparse.eval nodeValue1675 x + ((3 : ℝ) * Sparse.eval nodeValue1693 x + ((3 : ℝ) * Sparse.eval nodeValue1694 x + ((3 : ℝ) * Sparse.eval nodeValue1727 x + ((3 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((3 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))

def numericRow1322 : Integer.Sparse Master := [(Sum.inr 1519, 3), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 1675, 6), (Sum.inr 1693, 3), (Sum.inr 1694, 3), (Sum.inr 1728, 3), (Sum.inr 1756, 1), (Sum.inr 4084, 1)]

theorem reindexCheck1322 : Integer.Sparse.reindex keyMap MixedData.row1322 = numericRow1322 := by decide +kernel

theorem numericCheck1322 (x : Master → ℝ) : Integer.Sparse.eval numericRow1322 x =
    (1 : ℝ) * reducedSource1322 x := by
  norm_num [numericRow1322, reducedSource1322, Integer.Sparse.eval, Sparse.eval, nodeValue1519, nodeValue1538, nodeValue1539, nodeValue1675, nodeValue1693, nodeValue1694, nodeValue1727, nodeValue1728, nodeValue1754, nodeValue1756, nodeValue2229, nodeValue2293, nodeValue4084]

noncomputable def reducedSource1323 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue608 x + ((1 : ℝ) * Sparse.eval nodeValue619 x + ((1 : ℝ) * Sparse.eval nodeValue620 x + ((1 : ℝ) * Sparse.eval nodeValue1095 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow1323 : Integer.Sparse Master := [(Sum.inr 608, 3), (Sum.inr 619, 1), (Sum.inr 620, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1323 : Integer.Sparse.reindex keyMap MixedData.row1323 = numericRow1323 := by decide +kernel

theorem numericCheck1323 (x : Master → ℝ) : Integer.Sparse.eval numericRow1323 x =
    (1 : ℝ) * reducedSource1323 x := by
  norm_num [numericRow1323, reducedSource1323, Integer.Sparse.eval, Sparse.eval, nodeValue608, nodeValue619, nodeValue620, nodeValue1095, nodeValue4084]

noncomputable def reducedSource1324 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4071 x + ((3 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4284 x + ((6 : ℝ) * Sparse.eval nodeValue4404 x + ((3 : ℝ) * Sparse.eval nodeValue4431 x + ((3 : ℝ) * Sparse.eval nodeValue4432 x + ((3 : ℝ) * Sparse.eval nodeValue4466 x + ((3 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((3 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + 0))))))))))))

def numericRow1324 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, 4), (Sum.inl 7, 8), (Sum.inl 8, 8), (Sum.inl 1, 3), (Sum.inr 985, -432), (Sum.inr 1012, -216), (Sum.inr 1049, -216), (Sum.inr 1050, -216), (Sum.inr 1094, -72), (Sum.inr 1246, -216), (Sum.inr 1618, -432), (Sum.inr 1627, -216), (Sum.inr 1738, -216), (Sum.inr 1741, -72), (Sum.inr 1751, -216), (Sum.inr 3301, -216), (Sum.inr 3311, -72), (Sum.inr 3312, -72), (Sum.inr 4071, 288)]

theorem reindexCheck1324 : Integer.Sparse.reindex keyMap MixedData.row1324 = numericRow1324 := by decide +kernel

theorem numericCheck1324 (x : Master → ℝ) : Integer.Sparse.eval numericRow1324 x =
    (288 : ℝ) * reducedSource1324 x := by
  norm_num [numericRow1324, reducedSource1324, Integer.Sparse.eval, Sparse.eval, nodeValue4071, nodeValue4273, nodeValue4284, nodeValue4404, nodeValue4431, nodeValue4432, nodeValue4466, nodeValue4467, nodeValue4510, nodeValue4511, nodeValue4612, nodeValue4627, nodeValue4628]
  ring

noncomputable def reducedSource1325 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1012 x + ((1 : ℝ) * Sparse.eval nodeValue1953 x + ((2 : ℝ) * Sparse.eval nodeValue2006 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1325 : Integer.Sparse Master := [(Sum.inr 1012, 1), (Sum.inr 2006, 2), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1325 : Integer.Sparse.reindex keyMap MixedData.row1325 = numericRow1325 := by decide +kernel

theorem numericCheck1325 (x : Master → ℝ) : Integer.Sparse.eval numericRow1325 x =
    (1 : ℝ) * reducedSource1325 x := by
  norm_num [numericRow1325, reducedSource1325, Integer.Sparse.eval, Sparse.eval, nodeValue1012, nodeValue1953, nodeValue2006, nodeValue2228, nodeValue2230, nodeValue4081]

noncomputable def reducedSource1326 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4141 x + ((2 : ℝ) * Sparse.eval nodeValue4148 x + ((1 : ℝ) * Sparse.eval nodeValue4167 x + ((2 : ℝ) * Sparse.eval nodeValue4305 x + ((2 : ℝ) * Sparse.eval nodeValue4318 x + ((2 : ℝ) * Sparse.eval nodeValue4321 x + ((4 : ℝ) * Sparse.eval nodeValue4325 x + ((2 : ℝ) * Sparse.eval nodeValue4339 x + ((4 : ℝ) * Sparse.eval nodeValue4419 x + ((2 : ℝ) * Sparse.eval nodeValue4428 x + ((2 : ℝ) * Sparse.eval nodeValue4491 x + ((2 : ℝ) * Sparse.eval nodeValue4790 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + 0)))))))))))))

def numericRow1326 : Integer.Sparse Master := [(Sum.inr 569, -2), (Sum.inr 576, -2), (Sum.inr 595, -1), (Sum.inr 899, -2), (Sum.inr 903, -4), (Sum.inr 917, -2), (Sum.inr 1000, -4), (Sum.inr 1009, -2), (Sum.inr 1075, -2), (Sum.inr 1490, -2), (Sum.inr 1496, -2), (Sum.inr 1500, -1), (Sum.inr 1587, -2), (Sum.inr 1591, -4), (Sum.inr 1605, -4), (Sum.inr 1630, -2), (Sum.inr 1634, -2), (Sum.inr 1653, -2), (Sum.inr 4082, 4)]

theorem reindexCheck1326 : Integer.Sparse.reindex keyMap MixedData.row1326 = numericRow1326 := by decide +kernel

theorem numericCheck1326 (x : Master → ℝ) : Integer.Sparse.eval numericRow1326 x =
    (4 : ℝ) * reducedSource1326 x := by
  norm_num [numericRow1326, reducedSource1326, Integer.Sparse.eval, Sparse.eval, nodeValue4082, nodeValue4141, nodeValue4148, nodeValue4167, nodeValue4305, nodeValue4318, nodeValue4321, nodeValue4325, nodeValue4339, nodeValue4419, nodeValue4428, nodeValue4491, nodeValue4790, nodeValue4846]
  ring

noncomputable def reducedSource1327 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue569 x + ((2 : ℝ) * Sparse.eval nodeValue576 x + ((1 : ℝ) * Sparse.eval nodeValue595 x + ((1 : ℝ) * Sparse.eval nodeValue1013 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))

def numericRow1327 : Integer.Sparse Master := [(Sum.inr 569, 2), (Sum.inr 576, 2), (Sum.inr 595, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1327 : Integer.Sparse.reindex keyMap MixedData.row1327 = numericRow1327 := by decide +kernel

theorem numericCheck1327 (x : Master → ℝ) : Integer.Sparse.eval numericRow1327 x =
    (1 : ℝ) * reducedSource1327 x := by
  norm_num [numericRow1327, reducedSource1327, Integer.Sparse.eval, Sparse.eval, nodeValue569, nodeValue576, nodeValue595, nodeValue1013, nodeValue4082]

end MUB6.Certificate.MixedSourceBridge

end OAI
