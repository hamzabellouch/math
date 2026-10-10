import OAI.Analysis.MutuallyUnbiased.MixedData.Source10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1344 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue604 x + ((1 : ℝ) * Sparse.eval nodeValue923 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1344 : Integer.Sparse Master := [(Sum.inr 604, 1), (Sum.inr 923, 1), (Sum.inr 1042, 1), (Sum.inr 1058, 1), (Sum.inr 1079, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1344 : Integer.Sparse.reindex keyMap MixedData.row1344 = numericRow1344 := by decide +kernel

theorem numericCheck1344 (x : Master → ℝ) : Integer.Sparse.eval numericRow1344 x =
    (1 : ℝ) * reducedSource1344 x := by
  norm_num [numericRow1344, reducedSource1344, Integer.Sparse.eval, Sparse.eval, nodeValue604, nodeValue923, nodeValue1042, nodeValue1058, nodeValue1079, nodeValue1087, nodeValue4084]

noncomputable def reducedSource1345 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1335 x + ((1 : ℝ) * Sparse.eval nodeValue1337 x + ((1 : ℝ) * Sparse.eval nodeValue1338 x + ((1 : ℝ) * Sparse.eval nodeValue1347 x + ((1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1345 : Integer.Sparse Master := [(Sum.inr 1335, 1), (Sum.inr 1337, 1), (Sum.inr 1338, 1), (Sum.inr 1347, 1), (Sum.inr 1406, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1345 : Integer.Sparse.reindex keyMap MixedData.row1345 = numericRow1345 := by decide +kernel

theorem numericCheck1345 (x : Master → ℝ) : Integer.Sparse.eval numericRow1345 x =
    (1 : ℝ) * reducedSource1345 x := by
  norm_num [numericRow1345, reducedSource1345, Integer.Sparse.eval, Sparse.eval, nodeValue1335, nodeValue1337, nodeValue1338, nodeValue1347, nodeValue1406, nodeValue2954, nodeValue4091]

noncomputable def reducedSource1346 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2502 x + ((1 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1346 : Integer.Sparse Master := [(Sum.inr 1714, 1), (Sum.inr 2502, 1), (Sum.inr 3285, 1), (Sum.inr 3287, 1), (Sum.inr 3293, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1346 : Integer.Sparse.reindex keyMap MixedData.row1346 = numericRow1346 := by decide +kernel

theorem numericCheck1346 (x : Master → ℝ) : Integer.Sparse.eval numericRow1346 x =
    (1 : ℝ) * reducedSource1346 x := by
  norm_num [numericRow1346, reducedSource1346, Integer.Sparse.eval, Sparse.eval, nodeValue1714, nodeValue2502, nodeValue3285, nodeValue3287, nodeValue3293, nodeValue3305, nodeValue4069]

noncomputable def reducedSource1347 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue824 x + ((1 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1347 : Integer.Sparse Master := [(Sum.inr 824, 1), (Sum.inr 1607, 1), (Sum.inr 1656, 1), (Sum.inr 1714, 1), (Sum.inr 1737, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1347 : Integer.Sparse.reindex keyMap MixedData.row1347 = numericRow1347 := by decide +kernel

theorem numericCheck1347 (x : Master → ℝ) : Integer.Sparse.eval numericRow1347 x =
    (1 : ℝ) * reducedSource1347 x := by
  norm_num [numericRow1347, reducedSource1347, Integer.Sparse.eval, Sparse.eval, nodeValue824, nodeValue1607, nodeValue1656, nodeValue1714, nodeValue1737, nodeValue1739, nodeValue4069]

noncomputable def reducedSource1348 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1348 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 1714, 1), (Sum.inr 1715, 1), (Sum.inr 1724, 1), (Sum.inr 1737, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1348 : Integer.Sparse.reindex keyMap MixedData.row1348 = numericRow1348 := by decide +kernel

theorem numericCheck1348 (x : Master → ℝ) : Integer.Sparse.eval numericRow1348 x =
    (1 : ℝ) * reducedSource1348 x := by
  norm_num [numericRow1348, reducedSource1348, Integer.Sparse.eval, Sparse.eval, nodeValue1713, nodeValue1714, nodeValue1715, nodeValue1724, nodeValue1737, nodeValue3293, nodeValue4069]

noncomputable def reducedSource1349 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue1598 x + ((1 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1349 : Integer.Sparse Master := [(Sum.inr 807, 1), (Sum.inr 1646, 1), (Sum.inr 1714, 1), (Sum.inr 1724, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1349 : Integer.Sparse.reindex keyMap MixedData.row1349 = numericRow1349 := by decide +kernel

theorem numericCheck1349 (x : Master → ℝ) : Integer.Sparse.eval numericRow1349 x =
    (1 : ℝ) * reducedSource1349 x := by
  norm_num [numericRow1349, reducedSource1349, Integer.Sparse.eval, Sparse.eval, nodeValue807, nodeValue1598, nodeValue1646, nodeValue1714, nodeValue1724, nodeValue1728, nodeValue4069]

noncomputable def reducedSource1350 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue601 x + ((1 : ℝ) * Sparse.eval nodeValue920 x + ((1 : ℝ) * Sparse.eval nodeValue1057 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((2 : ℝ) * Sparse.eval nodeValue1083 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1350 : Integer.Sparse Master := [(Sum.inr 601, 1), (Sum.inr 1057, 1), (Sum.inr 1079, 1), (Sum.inr 1083, 2), (Sum.inr 4084, -1)]

theorem reindexCheck1350 : Integer.Sparse.reindex keyMap MixedData.row1350 = numericRow1350 := by decide +kernel

theorem numericCheck1350 (x : Master → ℝ) : Integer.Sparse.eval numericRow1350 x =
    (1 : ℝ) * reducedSource1350 x := by
  norm_num [numericRow1350, reducedSource1350, Integer.Sparse.eval, Sparse.eval, nodeValue601, nodeValue920, nodeValue1057, nodeValue1079, nodeValue1083, nodeValue4084]

noncomputable def reducedSource1351 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1316 x + ((1 : ℝ) * Sparse.eval nodeValue1320 x + ((2 : ℝ) * Sparse.eval nodeValue1322 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1351 : Integer.Sparse Master := [(Sum.inr 1316, 1), (Sum.inr 1320, 1), (Sum.inr 1322, 2), (Sum.inr 1370, 1), (Sum.inr 2884, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1351 : Integer.Sparse.reindex keyMap MixedData.row1351 = numericRow1351 := by decide +kernel

theorem numericCheck1351 (x : Master → ℝ) : Integer.Sparse.eval numericRow1351 x =
    (1 : ℝ) * reducedSource1351 x := by
  norm_num [numericRow1351, reducedSource1351, Integer.Sparse.eval, Sparse.eval, nodeValue1316, nodeValue1320, nodeValue1322, nodeValue1370, nodeValue2884, nodeValue4091]

noncomputable def reducedSource1352 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue3241 x + ((1 : ℝ) * Sparse.eval nodeValue3245 x + ((2 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1352 : Integer.Sparse Master := [(Sum.inr 1709, 1), (Sum.inr 3241, 1), (Sum.inr 3245, 1), (Sum.inr 3246, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1352 : Integer.Sparse.reindex keyMap MixedData.row1352 = numericRow1352 := by decide +kernel

theorem numericCheck1352 (x : Master → ℝ) : Integer.Sparse.eval numericRow1352 x =
    (1 : ℝ) * reducedSource1352 x := by
  norm_num [numericRow1352, reducedSource1352, Integer.Sparse.eval, Sparse.eval, nodeValue1709, nodeValue3241, nodeValue3245, nodeValue3246, nodeValue3299, nodeValue4069]

noncomputable def reducedSource1353 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1353 : Integer.Sparse Master := [(Sum.inr 1707, 1), (Sum.inr 1709, 1), (Sum.inr 1724, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1353 : Integer.Sparse.reindex keyMap MixedData.row1353 = numericRow1353 := by decide +kernel

theorem numericCheck1353 (x : Master → ℝ) : Integer.Sparse.eval numericRow1353 x =
    (1 : ℝ) * reducedSource1353 x := by
  norm_num [numericRow1353, reducedSource1353, Integer.Sparse.eval, Sparse.eval, nodeValue1705, nodeValue1707, nodeValue1709, nodeValue1724, nodeValue3299, nodeValue4069]

noncomputable def reducedSource1354 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue811 x + ((1 : ℝ) * Sparse.eval nodeValue1601 x + ((1 : ℝ) * Sparse.eval nodeValue1649 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1354 : Integer.Sparse Master := [(Sum.inr 811, 1), (Sum.inr 1601, 1), (Sum.inr 1649, 1), (Sum.inr 1709, 1), (Sum.inr 1715, 1), (Sum.inr 1724, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1354 : Integer.Sparse.reindex keyMap MixedData.row1354 = numericRow1354 := by decide +kernel

theorem numericCheck1354 (x : Master → ℝ) : Integer.Sparse.eval numericRow1354 x =
    (1 : ℝ) * reducedSource1354 x := by
  norm_num [numericRow1354, reducedSource1354, Integer.Sparse.eval, Sparse.eval, nodeValue811, nodeValue1601, nodeValue1649, nodeValue1709, nodeValue1715, nodeValue1724, nodeValue4069]

noncomputable def reducedSource1355 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1314 x + ((1 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue1318 x + ((1 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1355 : Integer.Sparse Master := [(Sum.inr 1314, 1), (Sum.inr 1317, 1), (Sum.inr 1318, 1), (Sum.inr 1321, 1), (Sum.inr 1367, 1), (Sum.inr 2881, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1355 : Integer.Sparse.reindex keyMap MixedData.row1355 = numericRow1355 := by decide +kernel

theorem numericCheck1355 (x : Master → ℝ) : Integer.Sparse.eval numericRow1355 x =
    (1 : ℝ) * reducedSource1355 x := by
  norm_num [numericRow1355, reducedSource1355, Integer.Sparse.eval, Sparse.eval, nodeValue1314, nodeValue1317, nodeValue1318, nodeValue1321, nodeValue1367, nodeValue2881, nodeValue4092]

noncomputable def reducedSource1356 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue2466 x + ((1 : ℝ) * Sparse.eval nodeValue3238 x + ((1 : ℝ) * Sparse.eval nodeValue3240 x + ((1 : ℝ) * Sparse.eval nodeValue3245 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1356 : Integer.Sparse Master := [(Sum.inr 1715, 1), (Sum.inr 2466, 1), (Sum.inr 3238, 1), (Sum.inr 3240, 1), (Sum.inr 3245, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1356 : Integer.Sparse.reindex keyMap MixedData.row1356 = numericRow1356 := by decide +kernel

theorem numericCheck1356 (x : Master → ℝ) : Integer.Sparse.eval numericRow1356 x =
    (1 : ℝ) * reducedSource1356 x := by
  norm_num [numericRow1356, reducedSource1356, Integer.Sparse.eval, Sparse.eval, nodeValue1715, nodeValue2466, nodeValue3238, nodeValue3240, nodeValue3245, nodeValue3293, nodeValue4069]

noncomputable def reducedSource1357 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue827 x + ((1 : ℝ) * Sparse.eval nodeValue1609 x + ((1 : ℝ) * Sparse.eval nodeValue1658 x + ((2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1357 : Integer.Sparse Master := [(Sum.inr 827, 1), (Sum.inr 1609, 1), (Sum.inr 1658, 1), (Sum.inr 1715, 2), (Sum.inr 1737, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1357 : Integer.Sparse.reindex keyMap MixedData.row1357 = numericRow1357 := by decide +kernel

theorem numericCheck1357 (x : Master → ℝ) : Integer.Sparse.eval numericRow1357 x =
    (1 : ℝ) * reducedSource1357 x := by
  norm_num [numericRow1357, reducedSource1357, Integer.Sparse.eval, Sparse.eval, nodeValue827, nodeValue1609, nodeValue1658, nodeValue1715, nodeValue1737, nodeValue4069]

noncomputable def reducedSource1358 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue578 x + ((1 : ℝ) * Sparse.eval nodeValue942 x + ((1 : ℝ) * Sparse.eval nodeValue1020 x + ((1 : ℝ) * Sparse.eval nodeValue1039 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1358 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 942, 1), (Sum.inr 1039, 1), (Sum.inr 1041, 2), (Sum.inr 4083, -1)]

theorem reindexCheck1358 : Integer.Sparse.reindex keyMap MixedData.row1358 = numericRow1358 := by decide +kernel

theorem numericCheck1358 (x : Master → ℝ) : Integer.Sparse.eval numericRow1358 x =
    (1 : ℝ) * reducedSource1358 x := by
  norm_num [numericRow1358, reducedSource1358, Integer.Sparse.eval, Sparse.eval, nodeValue578, nodeValue942, nodeValue1020, nodeValue1039, nodeValue1041, nodeValue4083]

noncomputable def reducedSource1359 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue3281 x + ((2 : ℝ) * Sparse.eval nodeValue3282 x + ((2 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1359 : Integer.Sparse Master := [(Sum.inr 3281, 1), (Sum.inr 3282, 2), (Sum.inr 3299, 2), (Sum.inr 4069, -1)]

theorem reindexCheck1359 : Integer.Sparse.reindex keyMap MixedData.row1359 = numericRow1359 := by decide +kernel

theorem numericCheck1359 (x : Master → ℝ) : Integer.Sparse.eval numericRow1359 x =
    (1 : ℝ) * reducedSource1359 x := by
  norm_num [numericRow1359, reducedSource1359, Integer.Sparse.eval, Sparse.eval, nodeValue1705, nodeValue3281, nodeValue3282, nodeValue3299, nodeValue4069]

end MUB6.Certificate.MixedSourceBridge

end OAI
