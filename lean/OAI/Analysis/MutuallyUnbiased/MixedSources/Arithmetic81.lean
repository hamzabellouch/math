import OAI.Analysis.MutuallyUnbiased.MixedData.Source10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1296 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue582 x + ((1 : ℝ) * Sparse.eval nodeValue588 x + ((1 : ℝ) * Sparse.eval nodeValue590 x + ((1 : ℝ) * Sparse.eval nodeValue613 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1296 : Integer.Sparse Master := [(Sum.inr 582, 2), (Sum.inr 588, 1), (Sum.inr 590, 1), (Sum.inr 613, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1296 : Integer.Sparse.reindex keyMap MixedData.row1296 = numericRow1296 := by decide +kernel

theorem numericCheck1296 (x : Master → ℝ) : Integer.Sparse.eval numericRow1296 x =
    (1 : ℝ) * reducedSource1296 x := by
  norm_num [numericRow1296, reducedSource1296, Integer.Sparse.eval, Sparse.eval, nodeValue582, nodeValue588, nodeValue590, nodeValue613, nodeValue1049, nodeValue4084]

noncomputable def reducedSource1297 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue613 x + ((2 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1297 : Integer.Sparse Master := [(Sum.inr 613, 1), (Sum.inr 932, 2), (Sum.inr 1049, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1297 : Integer.Sparse.reindex keyMap MixedData.row1297 = numericRow1297 := by decide +kernel

theorem numericCheck1297 (x : Master → ℝ) : Integer.Sparse.eval numericRow1297 x =
    (1 : ℝ) * reducedSource1297 x := by
  norm_num [numericRow1297, reducedSource1297, Integer.Sparse.eval, Sparse.eval, nodeValue613, nodeValue932, nodeValue1049, nodeValue1082, nodeValue1087, nodeValue4084]

noncomputable def reducedSource1298 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue946 x + ((1 : ℝ) * Sparse.eval nodeValue952 x + ((1 : ℝ) * Sparse.eval nodeValue954 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1298 : Integer.Sparse Master := [(Sum.inr 946, 2), (Sum.inr 952, 1), (Sum.inr 954, 1), (Sum.inr 1049, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1298 : Integer.Sparse.reindex keyMap MixedData.row1298 = numericRow1298 := by decide +kernel

theorem numericCheck1298 (x : Master → ℝ) : Integer.Sparse.eval numericRow1298 x =
    (1 : ℝ) * reducedSource1298 x := by
  norm_num [numericRow1298, reducedSource1298, Integer.Sparse.eval, Sparse.eval, nodeValue946, nodeValue952, nodeValue954, nodeValue1049, nodeValue2115, nodeValue4084]

noncomputable def reducedSource1299 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue582 x + ((1 : ℝ) * Sparse.eval nodeValue906 x + ((1 : ℝ) * Sparse.eval nodeValue946 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1299 : Integer.Sparse Master := [(Sum.inr 582, 1), (Sum.inr 906, 1), (Sum.inr 946, 1), (Sum.inr 1040, 1), (Sum.inr 1042, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1299 : Integer.Sparse.reindex keyMap MixedData.row1299 = numericRow1299 := by decide +kernel

theorem numericCheck1299 (x : Master → ℝ) : Integer.Sparse.eval numericRow1299 x =
    (1 : ℝ) * reducedSource1299 x := by
  norm_num [numericRow1299, reducedSource1299, Integer.Sparse.eval, Sparse.eval, nodeValue582, nodeValue906, nodeValue946, nodeValue1040, nodeValue1042, nodeValue1049, nodeValue4084]

noncomputable def reducedSource1300 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4106 x + ((1 : ℝ) * Sparse.eval nodeValue4109 x + ((1 : ℝ) * Sparse.eval nodeValue4111 x + ((1 : ℝ) * Sparse.eval nodeValue4132 x + ((2 : ℝ) * Sparse.eval nodeValue4291 x + ((2 : ℝ) * Sparse.eval nodeValue4294 x + ((2 : ℝ) * Sparse.eval nodeValue4296 x + ((2 : ℝ) * Sparse.eval nodeValue4313 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4359 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((2 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

def numericRow1300 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 5, -10), (Sum.inl 2, -10), (Sum.inl 7, -40), (Sum.inl 3, -80), (Sum.inl 1, 15), (Sum.inr 543, -2160), (Sum.inr 546, -1080), (Sum.inr 548, -1080), (Sum.inr 562, -1080), (Sum.inr 675, -2160), (Sum.inr 676, -1080), (Sum.inr 679, -1080), (Sum.inr 685, -1080), (Sum.inr 869, -2160), (Sum.inr 872, -2160), (Sum.inr 874, -2160), (Sum.inr 891, -2160), (Sum.inr 932, -2160), (Sum.inr 937, -1080), (Sum.inr 939, -1080), (Sum.inr 1035, -2160), (Sum.inr 1037, -1080), (Sum.inr 1044, -2160), (Sum.inr 1046, -1080), (Sum.inr 1075, -1080), (Sum.inr 1087, -1080), (Sum.inr 1561, -2160), (Sum.inr 1562, -2160), (Sum.inr 1565, -2160), (Sum.inr 1570, -2160), (Sum.inr 1645, -2160), (Sum.inr 1647, -1080), (Sum.inr 1653, -1080), (Sum.inr 1681, -2160), (Sum.inr 1683, -1080), (Sum.inr 1694, -1080), (Sum.inr 1737, -2160), (Sum.inr 1739, -1080), (Sum.inr 1750, -1080), (Sum.inr 2488, -2160), (Sum.inr 2765, -1080), (Sum.inr 3478, -2160), (Sum.inr 3582, -1080), (Sum.inr 3614, -1080), (Sum.inr 3632, -1080)]

theorem reindexCheck1300 : Integer.Sparse.reindex keyMap MixedData.row1300 = numericRow1300 := by decide +kernel

theorem numericCheck1300 (x : Master → ℝ) : Integer.Sparse.eval numericRow1300 x =
    (4320 : ℝ) * reducedSource1300 x := by
  norm_num [numericRow1300, reducedSource1300, Integer.Sparse.eval, Sparse.eval, nodeValue4106, nodeValue4109, nodeValue4111, nodeValue4132, nodeValue4291, nodeValue4294, nodeValue4296, nodeValue4313, nodeValue4354, nodeValue4359, nodeValue4361, nodeValue4452, nodeValue4454, nodeValue4461, nodeValue4463, nodeValue4491, nodeValue4503, nodeValue5080, nodeValue5176, nodeValue5291, nodeValue5294]; ring

noncomputable def reducedSource1301 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue543 x + ((1 : ℝ) * Sparse.eval nodeValue546 x + ((1 : ℝ) * Sparse.eval nodeValue548 x + ((1 : ℝ) * Sparse.eval nodeValue562 x + ((2 : ℝ) * Sparse.eval nodeValue869 x + ((2 : ℝ) * Sparse.eval nodeValue872 x + ((2 : ℝ) * Sparse.eval nodeValue874 x + ((2 : ℝ) * Sparse.eval nodeValue891 x + ((2 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue937 x + ((1 : ℝ) * Sparse.eval nodeValue939 x + ((2 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((2 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + 0))))))))))))))))))))

def numericRow1301 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 5, 10), (Sum.inl 2, 10), (Sum.inl 7, 40), (Sum.inl 3, 80), (Sum.inl 1, -15), (Sum.inr 543, 2160), (Sum.inr 546, 1080), (Sum.inr 548, 1080), (Sum.inr 562, 1080), (Sum.inr 869, 2160), (Sum.inr 872, 2160), (Sum.inr 874, 2160), (Sum.inr 891, 2160), (Sum.inr 932, 2160), (Sum.inr 937, 1080), (Sum.inr 939, 1080), (Sum.inr 1035, 2160), (Sum.inr 1037, 1080), (Sum.inr 1044, 2160), (Sum.inr 1046, 1080), (Sum.inr 1075, 1080), (Sum.inr 1087, 1080), (Sum.inr 2488, 2160), (Sum.inr 2765, 1080)]

theorem reindexCheck1301 : Integer.Sparse.reindex keyMap MixedData.row1301 = numericRow1301 := by decide +kernel

theorem numericCheck1301 (x : Master → ℝ) : Integer.Sparse.eval numericRow1301 x =
    (1080 : ℝ) * reducedSource1301 x := by
  norm_num [numericRow1301, reducedSource1301, Integer.Sparse.eval, Sparse.eval, nodeValue543, nodeValue546, nodeValue548, nodeValue562, nodeValue869, nodeValue872, nodeValue874, nodeValue891, nodeValue932, nodeValue937, nodeValue939, nodeValue1035, nodeValue1037, nodeValue1044, nodeValue1046, nodeValue1075, nodeValue1087, nodeValue2488, nodeValue2604, nodeValue2765, nodeValue2768]; ring

noncomputable def reducedSource1302 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4155 x + ((2 : ℝ) * Sparse.eval nodeValue4161 x + ((1 : ℝ) * Sparse.eval nodeValue4186 x + ((2 : ℝ) * Sparse.eval nodeValue4329 x + ((4 : ℝ) * Sparse.eval nodeValue4335 x + ((2 : ℝ) * Sparse.eval nodeValue4355 x + ((2 : ℝ) * Sparse.eval nodeValue4369 x + ((2 : ℝ) * Sparse.eval nodeValue4374 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + 0)))))))))))))

def numericRow1302 : Integer.Sparse Master := [(Sum.inr 614, -1), (Sum.inr 933, -2), (Sum.inr 1041, -4), (Sum.inr 1046, -2), (Sum.inr 1536, -1), (Sum.inr 1691, -2), (Sum.inr 1724, -4), (Sum.inr 1750, -2), (Sum.inr 2029, -2), (Sum.inr 2116, -1), (Sum.inr 2225, -2), (Sum.inr 2288, -1), (Sum.inr 4155, 8), (Sum.inr 4161, 8), (Sum.inr 4335, 16), (Sum.inr 4369, 8), (Sum.inr 4374, 8)]

theorem reindexCheck1302 : Integer.Sparse.reindex keyMap MixedData.row1302 = numericRow1302 := by decide +kernel

theorem numericCheck1302 (x : Master → ℝ) : Integer.Sparse.eval numericRow1302 x =
    (4 : ℝ) * reducedSource1302 x := by
  norm_num [numericRow1302, reducedSource1302, Integer.Sparse.eval, Sparse.eval, nodeValue4155, nodeValue4161, nodeValue4186, nodeValue4329, nodeValue4335, nodeValue4355, nodeValue4369, nodeValue4374, nodeValue4458, nodeValue4463, nodeValue4502, nodeValue4811, nodeValue4875, nodeValue4895]; ring

noncomputable def reducedSource1303 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue632 x + ((2 : ℝ) * Sparse.eval nodeValue635 x + ((1 : ℝ) * Sparse.eval nodeValue649 x + ((2 : ℝ) * Sparse.eval nodeValue1322 x + ((2 : ℝ) * Sparse.eval nodeValue1324 x + ((2 : ℝ) * Sparse.eval nodeValue1331 x + ((4 : ℝ) * Sparse.eval nodeValue1333 x + ((2 : ℝ) * Sparse.eval nodeValue1344 x + ((4 : ℝ) * Sparse.eval nodeValue1411 x + ((2 : ℝ) * Sparse.eval nodeValue1413 x + ((2 : ℝ) * Sparse.eval nodeValue1447 x + ((1 : ℝ) * Sparse.eval nodeValue3188 x + ((2 : ℝ) * Sparse.eval nodeValue3207 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))

def numericRow1303 : Integer.Sparse Master := [(Sum.inl 0, -12), (Sum.inl 5, 25), (Sum.inl 2, -15), (Sum.inl 8, -20), (Sum.inl 1, -20), (Sum.inr 632, 270), (Sum.inr 635, 270), (Sum.inr 1322, 270), (Sum.inr 1324, 270), (Sum.inr 1333, 540)]

theorem reindexCheck1303 : Integer.Sparse.reindex keyMap MixedData.row1303 = numericRow1303 := by decide +kernel

theorem numericCheck1303 (x : Master → ℝ) : Integer.Sparse.eval numericRow1303 x =
    (135 : ℝ) * reducedSource1303 x := by
  norm_num [numericRow1303, reducedSource1303, Integer.Sparse.eval, Sparse.eval, nodeValue632, nodeValue635, nodeValue649, nodeValue1322, nodeValue1324, nodeValue1331, nodeValue1333, nodeValue1344, nodeValue1411, nodeValue1413, nodeValue1447, nodeValue3188, nodeValue3207, nodeValue3229]; ring

noncomputable def reducedSource1304 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1515 x + ((2 : ℝ) * Sparse.eval nodeValue1533 x + ((1 : ℝ) * Sparse.eval nodeValue1536 x + ((2 : ℝ) * Sparse.eval nodeValue1671 x + ((4 : ℝ) * Sparse.eval nodeValue1689 x + ((2 : ℝ) * Sparse.eval nodeValue1691 x + ((2 : ℝ) * Sparse.eval nodeValue1721 x + ((4 : ℝ) * Sparse.eval nodeValue1724 x + ((2 : ℝ) * Sparse.eval nodeValue1748 x + ((2 : ℝ) * Sparse.eval nodeValue1750 x + ((2 : ℝ) * Sparse.eval nodeValue1753 x + ((2 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + 0)))))))))))))

def numericRow1304 : Integer.Sparse Master := [(Sum.inr 1515, 2), (Sum.inr 1533, 2), (Sum.inr 1536, 1), (Sum.inr 1689, 4), (Sum.inr 1691, 2), (Sum.inr 1721, 2), (Sum.inr 1724, 4), (Sum.inr 1748, 2), (Sum.inr 1750, 2), (Sum.inr 2225, 2), (Sum.inr 2288, 1)]

theorem reindexCheck1304 : Integer.Sparse.reindex keyMap MixedData.row1304 = numericRow1304 := by decide +kernel

theorem numericCheck1304 (x : Master → ℝ) : Integer.Sparse.eval numericRow1304 x =
    (1 : ℝ) * reducedSource1304 x := by
  norm_num [numericRow1304, reducedSource1304, Integer.Sparse.eval, Sparse.eval, nodeValue1515, nodeValue1533, nodeValue1536, nodeValue1671, nodeValue1689, nodeValue1691, nodeValue1721, nodeValue1724, nodeValue1748, nodeValue1750, nodeValue1753, nodeValue2225, nodeValue2288, nodeValue2291]

noncomputable def reducedSource1305 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue583 x + ((2 : ℝ) * Sparse.eval nodeValue589 x + ((1 : ℝ) * Sparse.eval nodeValue614 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow1305 : Integer.Sparse Master := [(Sum.inr 583, 2), (Sum.inr 589, 2), (Sum.inr 614, 1), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1305 : Integer.Sparse.reindex keyMap MixedData.row1305 = numericRow1305 := by decide +kernel

theorem numericCheck1305 (x : Master → ℝ) : Integer.Sparse.eval numericRow1305 x =
    (1 : ℝ) * reducedSource1305 x := by
  norm_num [numericRow1305, reducedSource1305, Integer.Sparse.eval, Sparse.eval, nodeValue583, nodeValue589, nodeValue614, nodeValue1050, nodeValue4083]

noncomputable def reducedSource1306 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue614 x + ((2 : ℝ) * Sparse.eval nodeValue933 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((2 : ℝ) * Sparse.eval nodeValue1086 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow1306 : Integer.Sparse Master := [(Sum.inr 614, 1), (Sum.inr 933, 2), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1306 : Integer.Sparse.reindex keyMap MixedData.row1306 = numericRow1306 := by decide +kernel

theorem numericCheck1306 (x : Master → ℝ) : Integer.Sparse.eval numericRow1306 x =
    (1 : ℝ) * reducedSource1306 x := by
  norm_num [numericRow1306, reducedSource1306, Integer.Sparse.eval, Sparse.eval, nodeValue614, nodeValue933, nodeValue1050, nodeValue1086, nodeValue4083]

noncomputable def reducedSource1307 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue947 x + ((2 : ℝ) * Sparse.eval nodeValue953 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow1307 : Integer.Sparse Master := [(Sum.inr 947, 2), (Sum.inr 953, 2), (Sum.inr 1050, 1), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1307 : Integer.Sparse.reindex keyMap MixedData.row1307 = numericRow1307 := by decide +kernel

theorem numericCheck1307 (x : Master → ℝ) : Integer.Sparse.eval numericRow1307 x =
    (1 : ℝ) * reducedSource1307 x := by
  norm_num [numericRow1307, reducedSource1307, Integer.Sparse.eval, Sparse.eval, nodeValue947, nodeValue953, nodeValue1050, nodeValue2116, nodeValue4083]

noncomputable def reducedSource1308 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue583 x + ((1 : ℝ) * Sparse.eval nodeValue907 x + ((1 : ℝ) * Sparse.eval nodeValue947 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1308 : Integer.Sparse Master := [(Sum.inr 583, 1), (Sum.inr 947, 1), (Sum.inr 1041, 2), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1308 : Integer.Sparse.reindex keyMap MixedData.row1308 = numericRow1308 := by decide +kernel

theorem numericCheck1308 (x : Master → ℝ) : Integer.Sparse.eval numericRow1308 x =
    (1 : ℝ) * reducedSource1308 x := by
  norm_num [numericRow1308, reducedSource1308, Integer.Sparse.eval, Sparse.eval, nodeValue583, nodeValue907, nodeValue947, nodeValue1041, nodeValue1050, nodeValue4083]

noncomputable def reducedSource1309 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4107 x + ((2 : ℝ) * Sparse.eval nodeValue4110 x + ((1 : ℝ) * Sparse.eval nodeValue4133 x + ((2 : ℝ) * Sparse.eval nodeValue4292 x + ((4 : ℝ) * Sparse.eval nodeValue4295 x + ((2 : ℝ) * Sparse.eval nodeValue4314 x + ((2 : ℝ) * Sparse.eval nodeValue4355 x + ((2 : ℝ) * Sparse.eval nodeValue4360 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + 0)))))))))))))

def numericRow1309 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 5, -5), (Sum.inl 2, -15), (Sum.inl 8, -20), (Sum.inl 1, -20), (Sum.inr 544, -1080), (Sum.inr 547, -1080), (Sum.inr 563, -540), (Sum.inr 682, -1080), (Sum.inr 684, -1080), (Sum.inr 692, -540), (Sum.inr 870, -1080), (Sum.inr 873, -2160), (Sum.inr 892, -1080), (Sum.inr 933, -1080), (Sum.inr 938, -1080), (Sum.inr 1041, -2160), (Sum.inr 1043, -1080), (Sum.inr 1083, -1080), (Sum.inr 1567, -1080), (Sum.inr 1569, -2160), (Sum.inr 1575, -1080), (Sum.inr 1691, -1080), (Sum.inr 1693, -1080), (Sum.inr 1724, -2160), (Sum.inr 1725, -1080), (Sum.inr 1728, -1080), (Sum.inr 2489, -1080), (Sum.inr 3482, -1080), (Sum.inr 3616, -540), (Sum.inr 3627, -1080)]

theorem reindexCheck1309 : Integer.Sparse.reindex keyMap MixedData.row1309 = numericRow1309 := by decide +kernel

theorem numericCheck1309 (x : Master → ℝ) : Integer.Sparse.eval numericRow1309 x =
    (2160 : ℝ) * reducedSource1309 x := by
  norm_num [numericRow1309, reducedSource1309, Integer.Sparse.eval, Sparse.eval, nodeValue4107, nodeValue4110, nodeValue4133, nodeValue4292, nodeValue4295, nodeValue4314, nodeValue4355, nodeValue4360, nodeValue4458, nodeValue4460, nodeValue4499, nodeValue5081, nodeValue5177, nodeValue5293]; ring

noncomputable def reducedSource1310 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4256 x + ((2 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((2 : ℝ) * Sparse.eval nodeValue4393 x + ((4 : ℝ) * Sparse.eval nodeValue4404 x + ((2 : ℝ) * Sparse.eval nodeValue4412 x + ((4 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4467 x + ((2 : ℝ) * Sparse.eval nodeValue4480 x + ((2 : ℝ) * Sparse.eval nodeValue4511 x + ((2 : ℝ) * Sparse.eval nodeValue4593 x + ((2 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + 0)))))))))))))

def numericRow1310 : Integer.Sparse Master := [(Sum.inl 0, 3), (Sum.inl 5, 10), (Sum.inl 8, 40), (Sum.inl 1, -5), (Sum.inr 790, -720), (Sum.inr 831, -360), (Sum.inr 848, -720), (Sum.inr 858, -360), (Sum.inr 985, -1440), (Sum.inr 1049, -720), (Sum.inr 1050, -720), (Sum.inr 1246, -720), (Sum.inr 1618, -1440), (Sum.inr 1738, -720), (Sum.inr 1751, -720), (Sum.inr 3301, -720), (Sum.inr 3312, -360), (Sum.inr 4412, 2880), (Sum.inr 4444, 5760), (Sum.inr 4480, 2880), (Sum.inr 4593, 2880)]

theorem reindexCheck1310 : Integer.Sparse.reindex keyMap MixedData.row1310 = numericRow1310 := by decide +kernel

theorem numericCheck1310 (x : Master → ℝ) : Integer.Sparse.eval numericRow1310 x =
    (1440 : ℝ) * reducedSource1310 x := by
  norm_num [numericRow1310, reducedSource1310, Integer.Sparse.eval, Sparse.eval, nodeValue4256, nodeValue4273, nodeValue4279, nodeValue4393, nodeValue4404, nodeValue4412, nodeValue4444, nodeValue4466, nodeValue4467, nodeValue4480, nodeValue4511, nodeValue4593, nodeValue4612, nodeValue4628]; ring

noncomputable def reducedSource1311 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue790 x + ((2 : ℝ) * Sparse.eval nodeValue816 x + ((1 : ℝ) * Sparse.eval nodeValue831 x + ((2 : ℝ) * Sparse.eval nodeValue974 x + ((4 : ℝ) * Sparse.eval nodeValue985 x + ((2 : ℝ) * Sparse.eval nodeValue993 x + ((4 : ℝ) * Sparse.eval nodeValue1026 x + ((2 : ℝ) * Sparse.eval nodeValue1049 x + ((2 : ℝ) * Sparse.eval nodeValue1050 x + ((2 : ℝ) * Sparse.eval nodeValue1063 x + ((2 : ℝ) * Sparse.eval nodeValue1095 x + ((2 : ℝ) * Sparse.eval nodeValue1220 x + ((2 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + 0)))))))))))))

def numericRow1311 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 5, -110), (Sum.inl 7, 80), (Sum.inl 8, -40), (Sum.inl 1, 45), (Sum.inr 790, 2160), (Sum.inr 831, 1080), (Sum.inr 985, 4320), (Sum.inr 993, 2160), (Sum.inr 1026, 4320), (Sum.inr 1049, 2160), (Sum.inr 1050, 2160), (Sum.inr 1063, 2160), (Sum.inr 1220, 2160)]

theorem reindexCheck1311 : Integer.Sparse.reindex keyMap MixedData.row1311 = numericRow1311 := by decide +kernel

theorem numericCheck1311 (x : Master → ℝ) : Integer.Sparse.eval numericRow1311 x =
    (1080 : ℝ) * reducedSource1311 x := by
  norm_num [numericRow1311, reducedSource1311, Integer.Sparse.eval, Sparse.eval, nodeValue790, nodeValue816, nodeValue831, nodeValue974, nodeValue985, nodeValue993, nodeValue1026, nodeValue1049, nodeValue1050, nodeValue1063, nodeValue1095, nodeValue1220, nodeValue1274, nodeValue1312]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
