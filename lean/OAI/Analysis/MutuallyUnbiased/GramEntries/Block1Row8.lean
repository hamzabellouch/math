import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block34
import OAI.Analysis.MutuallyUnbiased.GramRows.Block35

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1350, row1351, row1352, row1353, row1354, row1355, row1356, row1357, row1358, row1359, row1360, row1361, row1362, row1363]

theorem entryCheck8_0 : entry8_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_0 k)) := by decide +kernel

theorem rowsSound8_0 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1350 x
  · exact rowEval1351 x
  · exact rowEval1352 x
  · exact rowEval1353 x
  · exact rowEval1354 x
  · exact rowEval1355 x
  · exact rowEval1356 x
  · exact rowEval1357 x
  · exact rowEval1358 x
  · exact rowEval1359 x
  · exact rowEval1360 x
  · exact rowEval1361 x
  · exact rowEval1362 x
  · exact rowEval1363 x

theorem entryEval8_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_0 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck8_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_0]

def rows8_1 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1364, row1365, row1366, row1367, row1368, row1369, row1370, row1371, row1372, row1373, row1374, row1375, row1376, row1377]

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

theorem rowsSound8_1 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1364 x
  · exact rowEval1365 x
  · exact rowEval1366 x
  · exact rowEval1367 x
  · exact rowEval1368 x
  · exact rowEval1369 x
  · exact rowEval1370 x
  · exact rowEval1371 x
  · exact rowEval1372 x
  · exact rowEval1373 x
  · exact rowEval1374 x
  · exact rowEval1375 x
  · exact rowEval1376 x
  · exact rowEval1377 x

theorem entryEval8_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_1 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck8_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_1]

def rows8_2 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1378, row1379, row1380, row1381, row1382, row1383, row1384, row1385, row1386, row1387, row1388, row1389, row1390, row1391]

theorem entryCheck8_2 : entry8_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_2 k)) := by decide +kernel

theorem rowsSound8_2 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1378 x
  · exact rowEval1379 x
  · exact rowEval1380 x
  · exact rowEval1381 x
  · exact rowEval1382 x
  · exact rowEval1383 x
  · exact rowEval1384 x
  · exact rowEval1385 x
  · exact rowEval1386 x
  · exact rowEval1387 x
  · exact rowEval1388 x
  · exact rowEval1389 x
  · exact rowEval1390 x
  · exact rowEval1391 x

theorem entryEval8_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_2 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck8_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_2]

def rows8_3 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1392, row1393, row1394, row1395, row1396, row1397, row1398, row1399, row1400, row1401, row1402, row1403, row1404, row1405]

theorem entryCheck8_3 : entry8_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_3 k)) := by decide +kernel

theorem rowsSound8_3 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1392 x
  · exact rowEval1393 x
  · exact rowEval1394 x
  · exact rowEval1395 x
  · exact rowEval1396 x
  · exact rowEval1397 x
  · exact rowEval1398 x
  · exact rowEval1399 x
  · exact rowEval1400 x
  · exact rowEval1401 x
  · exact rowEval1402 x
  · exact rowEval1403 x
  · exact rowEval1404 x
  · exact rowEval1405 x

theorem entryEval8_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_3 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck8_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_3]

def rows8_4 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1406, row1407, row1408, row1409, row1410, row1411, row1412, row1413, row1414, row1415, row1416, row1417, row1418, row1419]

theorem entryCheck8_4 : entry8_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_4 k)) := by decide +kernel

theorem rowsSound8_4 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1406 x
  · exact rowEval1407 x
  · exact rowEval1408 x
  · exact rowEval1409 x
  · exact rowEval1410 x
  · exact rowEval1411 x
  · exact rowEval1412 x
  · exact rowEval1413 x
  · exact rowEval1414 x
  · exact rowEval1415 x
  · exact rowEval1416 x
  · exact rowEval1417 x
  · exact rowEval1418 x
  · exact rowEval1419 x

theorem entryEval8_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_4 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck8_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_4]

def rows8_5 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1420, row1421, row1422, row1423, row1424, row1425, row1426, row1427, row1428, row1429, row1430, row1431, row1432, row1433]

theorem entryCheck8_5 : entry8_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_5 k)) := by decide +kernel

theorem rowsSound8_5 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1420 x
  · exact rowEval1421 x
  · exact rowEval1422 x
  · exact rowEval1423 x
  · exact rowEval1424 x
  · exact rowEval1425 x
  · exact rowEval1426 x
  · exact rowEval1427 x
  · exact rowEval1428 x
  · exact rowEval1429 x
  · exact rowEval1430 x
  · exact rowEval1431 x
  · exact rowEval1432 x
  · exact rowEval1433 x

theorem entryEval8_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_5 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck8_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_5]

def rows8_6 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1434, row1435, row1436, row1437, row1438, row1439, row1440, row1441, row1442, row1443, row1444, row1445, row1446, row1447]

theorem entryCheck8_6 : entry8_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_6 k)) := by decide +kernel

theorem rowsSound8_6 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval1434 x
  · exact rowEval1435 x
  · exact rowEval1436 x
  · exact rowEval1437 x
  · exact rowEval1438 x
  · exact rowEval1439 x
  · exact rowEval1440 x
  · exact rowEval1441 x
  · exact rowEval1442 x
  · exact rowEval1443 x
  · exact rowEval1444 x
  · exact rowEval1445 x
  · exact rowEval1446 x
  · exact rowEval1447 x

theorem entryEval8_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_6 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck8_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_6]

def rows8_7 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1448, row1449, row1450, row1451, row1452, row1453, row1454, row1455, row1456, row1457, row1458, row1459, row1460, row1461]

theorem entryCheck8_7 : entry8_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_7 k)) := by decide +kernel

theorem rowsSound8_7 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval1448 x
  · exact rowEval1449 x
  · exact rowEval1450 x
  · exact rowEval1451 x
  · exact rowEval1452 x
  · exact rowEval1453 x
  · exact rowEval1454 x
  · exact rowEval1455 x
  · exact rowEval1456 x
  · exact rowEval1457 x
  · exact rowEval1458 x
  · exact rowEval1459 x
  · exact rowEval1460 x
  · exact rowEval1461 x

theorem entryEval8_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_7 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck8_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_7]

def rows8_8 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1462, row1463, row1464, row1465, row1466, row1467, row1468, row1469, row1470, row1471, row1472, row1473, row1474, row1475]

theorem entryCheck8_8 : entry8_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_8 k)) := by decide +kernel

theorem rowsSound8_8 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval1462 x
  · exact rowEval1463 x
  · exact rowEval1464 x
  · exact rowEval1465 x
  · exact rowEval1466 x
  · exact rowEval1467 x
  · exact rowEval1468 x
  · exact rowEval1469 x
  · exact rowEval1470 x
  · exact rowEval1471 x
  · exact rowEval1472 x
  · exact rowEval1473 x
  · exact rowEval1474 x
  · exact rowEval1475 x

theorem entryEval8_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_8 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck8_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_8]

end MUB6.Certificate.GramEntries.Block1

end OAI
