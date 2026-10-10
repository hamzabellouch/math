import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures1165To1383

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
lemma b1383 : Encl e1383 (11604671613 / 31250000000 : ℝ) (46418686453 / 125000000000 : ℝ) := by
  apply Encl.arcsin (z := e1327) (a := (46552505261 / 500000000000 : ℝ)) (b := (23276252631 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (362873270249 / 1000000000000 : ℝ) by norm_num).trans b1327.1
        exact b1327.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1327) (46552505261 / 500000000000 : ℝ) (23276252631 / 250000000000 : ℝ) from b1382) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1384 : ℝ := e59 * e1383
lemma b1384 : Encl e1384 (47347060181 / 250000000000 : ℝ) (189388240729 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1383 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1385 : ℝ := e61 * e1327
lemma b1385 : Encl e1385 (88903951211 / 500000000000 : ℝ) (177807902423 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1327 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1386 : ℝ := e1385 * e1344
lemma b1386 : Encl e1386 (20711031131 / 125000000000 : ℝ) (3313764981 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b1385 b1344 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1387 : ℝ := e1384 - e1386
lemma b1387 : Encl e1387 (11849995837 / 500000000000 : ℝ) (23699991681 / 1000000000000 : ℝ) := by
  exact Encl.sub b1384 b1386 (by norm_num) (by norm_num)

def e1388 : ℝ := e43 * e1344
lemma b1388 : Encl e1388 (186367699963 / 4000000000 : ℝ) (116479812477 / 2500000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1344 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1389 : ℝ := e1327 / e1388
lemma b1389 : Encl e1389 (1947082409 / 250000000000 : ℝ) (7788329637 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1327 b1388 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1390 : ℝ := e1387 - e1389
lemma b1390 : Encl e1390 (15911662037 / 1000000000000 : ℝ) (3182332409 / 200000000000 : ℝ) := by
  exact Encl.sub b1387 b1389 (by norm_num) (by norm_num)

def e1391 : ℝ := e1375 - e1390
lemma b1391 : Encl e1391 (173687216393 / 1000000000000 : ℝ) (5427725513 / 31250000000 : ℝ) := by
  exact Encl.sub b1375 b1390 (by norm_num) (by norm_num)

def e1392 : ℝ := e1391 / e1326
lemma b1392 : Encl e1392 (76178603681 / 500000000000 : ℝ) (152357207383 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1391 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1393 : ℝ := e1357 + e1392
lemma b1393 : Encl e1393 (-67132340553 / 250000000000 : ℝ) (-268529362173 / 1000000000000 : ℝ) := by
  exact Encl.add b1357 b1392 (by norm_num) (by norm_num)

def e1394 : ℝ := e1328 + e4
lemma b1394 : Encl e1394 (44171751209 / 25000000000 : ℝ) (1766870048363 / 1000000000000 : ℝ) := by
  exact Encl.add b1328 b4 (by norm_num) (by norm_num)

def e1395 : ℝ := e1394 / e23
lemma b1395 : Encl e1395 (44171751209 / 50000000000 : ℝ) (441717512091 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1394 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1396 : ℝ := e1328 / e1326
lemma b1396 : Encl e1396 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1328 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1397 : ℝ := e89 * e1396
lemma b1397 : Encl e1397 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1396 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1398 : ℝ := e1396 ^ 2
lemma b1398 : Encl e1398 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1396 (by norm_num) 2 (by norm_num) (by norm_num)

def e1399 : ℝ := e91 * e1398
lemma b1399 : Encl e1399 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1398 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1400 : ℝ := e5 + e1399
lemma b1400 : Encl e1400 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1399 (by norm_num) (by norm_num)

def e1401 : ℝ := Real.sqrt e1400
lemma b1401 : Encl e1401 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1400 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1402 : ℝ := e1397 * e1401
lemma b1402 : Encl e1402 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1397 b1401 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1403 : ℝ := e97 * e1398
lemma b1403 : Encl e1403 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1398 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1404 : ℝ := e1402 - e1403
lemma b1404 : Encl e1404 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1402 b1403 (by norm_num) (by norm_num)

def e1405 : ℝ := e1395 * e1404
lemma b1405 : Encl e1405 (150557230543 / 250000000000 : ℝ) (120445784439 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1395 b1404 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1406 : ℝ := e1395 / e1326
lemma b1406 : Encl e1406 (387471501833 / 500000000000 : ℝ) (774943003669 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1395 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1407 : ℝ := e89 * e1406
lemma b1407 : Encl e1407 (1373550711079 / 1000000000000 : ℝ) (686775355543 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1406 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1408 : ℝ := e1406 ^ 2
lemma b1408 : Encl e1408 (60053665893 / 100000000000 : ℝ) (75067082367 / 125000000000 : ℝ) := by
  exact Encl.pow b1406 (by norm_num) 2 (by norm_num) (by norm_num)

def e1409 : ℝ := e91 * e1408
lemma b1409 : Encl e1409 (29478774311 / 62500000000 : ℝ) (235830194491 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1408 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1410 : ℝ := e5 + e1409
lemma b1410 : Encl e1410 (91978774311 / 62500000000 : ℝ) (735830194491 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1409 (by norm_num) (by norm_num)

def e1411 : ℝ := Real.sqrt e1410
lemma b1411 : Encl e1411 (606560052463 / 500000000000 : ℝ) (1213120104929 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1410 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1412 : ℝ := e1407 * e1411
lemma b1412 : Encl e1412 (333256396549 / 200000000000 : ℝ) (833140991379 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1407 b1411 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1413 : ℝ := e97 * e1408
lemma b1413 : Encl e1413 (29478774311 / 31250000000 : ℝ) (943320777963 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1408 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1414 : ℝ := e1412 - e1413
lemma b1414 : Encl e1414 (361480602391 / 500000000000 : ℝ) (361480602403 / 500000000000 : ℝ) := by
  exact Encl.sub b1412 b1413 (by norm_num) (by norm_num)

def e1415 : ℝ := e1328 * e1414
lemma b1415 : Encl e1415 (70229059601 / 125000000000 : ℝ) (561832476829 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1328 b1414 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1416 : ℝ := e1405 - e1415
lemma b1416 : Encl e1416 (40396445343 / 1000000000000 : ℝ) (40396445387 / 1000000000000 : ℝ) := by
  exact Encl.sub b1405 b1415 (by norm_num) (by norm_num)

def e1417 : ℝ := e1395 ^ 2
lemma b1417 : Encl e1417 (780457441947 / 1000000000000 : ℝ) (24389295061 / 31250000000 : ℝ) := by
  exact Encl.pow b1395 (by norm_num) 2 (by norm_num) (by norm_num)

def e1418 : ℝ := e8 * e1417
lemma b1418 : Encl e1418 (191212073277 / 250000000000 : ℝ) (764848293113 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1419 : ℝ := e5 - e1418
lemma b1419 : Encl e1419 (235151706887 / 1000000000000 : ℝ) (58787926723 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b1418 (by norm_num) (by norm_num)

def e1420 : ℝ := e5 - e1417
lemma b1420 : Encl e1420 (6860704939 / 31250000000 : ℝ) (219542558053 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1417 (by norm_num) (by norm_num)

def e1421 : ℝ := Real.sqrt e1420
lemma b1421 : Encl e1421 (117138421869 / 250000000000 : ℝ) (468553687483 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1420 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1422 : ℝ := e1419 / e1421
lemma b1422 : Encl e1422 (20074686267 / 40000000000 : ℝ) (250933578347 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1419 b1421 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1423 : ℝ := e5 - e1422
lemma b1423 : Encl e1423 (249066421653 / 500000000000 : ℝ) (19925313733 / 40000000000 : ℝ) := by
  exact Encl.sub b5 b1422 (by norm_num) (by norm_num)

def e1424 : ℝ := e8 * e1358
lemma b1424 : Encl e1424 (591847435009 / 1000000000000 : ℝ) (118369487003 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1358 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1425 : ℝ := e5 - e1424
lemma b1425 : Encl e1425 (81630512997 / 200000000000 : ℝ) (408152564991 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1424 (by norm_num) (by norm_num)

def e1426 : ℝ := e1425 / e1360
lemma b1426 : Encl e1426 (648536372033 / 1000000000000 : ℝ) (648536372049 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1425 b1360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1427 : ℝ := e5 - e1426
lemma b1427 : Encl e1427 (351463627951 / 1000000000000 : ℝ) (351463627967 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1426 (by norm_num) (by norm_num)

def e1428 : ℝ := e1423 - e1427
lemma b1428 : Encl e1428 (146669215339 / 1000000000000 : ℝ) (73334607687 / 500000000000 : ℝ) := by
  exact Encl.sub b1423 b1427 (by norm_num) (by norm_num)

def e1429 : ℝ := e1416 * e1428
lemma b1429 : Encl e1429 (296245747 / 50000000000 : ℝ) (5924914949 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1416 b1428 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1430 : ℝ := e1414 - e1404
lemma b1430 : Encl e1430 (20635545477 / 500000000000 : ℝ) (41271091001 / 1000000000000 : ℝ) := by
  exact Encl.sub b1414 b1404 (by norm_num) (by norm_num)

def e1431 : ℝ := e5 + e1421
lemma b1431 : Encl e1431 (367138421869 / 250000000000 : ℝ) (1468553687483 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1421 (by norm_num) (by norm_num)

def e1432 : ℝ := e1395 / e1431
lemma b1432 : Encl e1432 (300784040689 / 500000000000 : ℝ) (601568081383 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1395 b1431 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1433 : ℝ := e1432 ^ 2
lemma b1433 : Encl e1433 (90471039133 / 250000000000 : ℝ) (361884156539 / 1000000000000 : ℝ) := by
  exact Encl.pow b1432 (by norm_num) 2 (by norm_num) (by norm_num)

def e1434 : ℝ := e5 + e1433
lemma b1434 : Encl e1434 (340471039133 / 250000000000 : ℝ) (1361884156539 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1433 (by norm_num) (by norm_num)

def e1435 : ℝ := Real.sqrt e1434
lemma b1435 : Encl e1435 (1166997924819 / 1000000000000 : ℝ) (1166997924823 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1434 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1436 : ℝ := e5 + e1435
lemma b1436 : Encl e1436 (2166997924819 / 1000000000000 : ℝ) (2166997924823 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1435 (by norm_num) (by norm_num)

def e1437 : ℝ := e1432 / e1436
lemma b1437 : Encl e1437 (69401091077 / 250000000000 : ℝ) (34700545539 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1432 b1436 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1438 : ℝ := Real.arcsin e1395
lemma b1438 : Encl e1438 (1083143407353 / 1000000000000 : ℝ) (108314340737 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e1395) (a := (69401091077 / 250000000000 : ℝ)) (b := (34700545539 / 125000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (44171751209 / 50000000000 : ℝ) by norm_num).trans b1395.1
        exact b1395.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1395) (69401091077 / 250000000000 : ℝ) (34700545539 / 125000000000 : ℝ) from b1437) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1439 : ℝ := e59 * e1438
lemma b1439 : Encl e1439 (2209612551 / 4000000000 : ℝ) (552403137759 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1438 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1440 : ℝ := e61 * e1395
lemma b1440 : Encl e1440 (54110395231 / 125000000000 : ℝ) (8657663237 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1395 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1441 : ℝ := e1440 * e1421
lemma b1441 : Encl e1441 (20282900173 / 100000000000 : ℝ) (40565800347 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1440 b1421 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1442 : ℝ := e1439 - e1441
lemma b1442 : Encl e1442 (69914827203 / 200000000000 : ℝ) (349574136029 / 1000000000000 : ℝ) := by
  exact Encl.sub b1439 b1441 (by norm_num) (by norm_num)

def e1443 : ℝ := e43 * e1421
lemma b1443 : Encl e1443 (117138421869 / 5000000000 : ℝ) (468553687483 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1421 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1444 : ℝ := e1395 / e1443
lemma b1444 : Encl e1444 (37709020237 / 1000000000000 : ℝ) (37709020239 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1395 b1443 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1445 : ℝ := e1442 - e1444
lemma b1445 : Encl e1445 (2436446217 / 7812500000 : ℝ) (19491569737 / 62500000000 : ℝ) := by
  exact Encl.sub b1442 b1444 (by norm_num) (by norm_num)

def e1446 : ℝ := e1445 - e1375
lemma b1446 : Encl e1446 (122266237323 / 1000000000000 : ℝ) (61133118677 / 500000000000 : ℝ) := by
  exact Encl.sub b1445 b1375 (by norm_num) (by norm_num)

def e1447 : ℝ := e1430 * e1446
lemma b1447 : Encl e1447 (5046061001 / 1000000000000 : ℝ) (5046061009 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1430 b1446 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1448 : ℝ := e1429 + e1447
lemma b1448 : Encl e1448 (10970975941 / 1000000000000 : ℝ) (5485487979 / 500000000000 : ℝ) := by
  exact Encl.add b1429 b1447 (by norm_num) (by norm_num)

def e1449 : ℝ := e1395 - e1328
lemma b1449 : Encl e1449 (26577073607 / 250000000000 : ℝ) (3322134201 / 31250000000 : ℝ) := by
  exact Encl.sub b1395 b1328 (by norm_num) (by norm_num)

def e1450 : ℝ := e1448 / e1449
lemma b1450 : Encl e1450 (51599811659 / 500000000000 : ℝ) (103199623483 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1448 b1449 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1451 : ℝ := e1393 + e1450
lemma b1451 : Encl e1451 (-82664869447 / 500000000000 : ℝ) (-16532973869 / 100000000000 : ℝ) := by
  exact Encl.add b1393 b1450 (by norm_num) (by norm_num)

def e1452 : ℝ := e4 * e1414
lemma b1452 : Encl e1452 (715546022047 / 1000000000000 : ℝ) (89443252759 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1414 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1453 : ℝ := e4 / e1326
lemma b1453 : Encl e1453 (868195893517 / 1000000000000 : ℝ) (868195893519 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1454 : ℝ := e89 * e1453
lemma b1454 : Encl e1454 (384709288701 / 250000000000 : ℝ) (1538837154809 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1453 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1455 : ℝ := e1453 ^ 2
lemma b1455 : Encl e1455 (753764109519 / 1000000000000 : ℝ) (188441027381 / 250000000000 : ℝ) := by
  exact Encl.pow b1453 (by norm_num) 2 (by norm_num) (by norm_num)

def e1456 : ℝ := e91 * e1455
lemma b1456 : Encl e1456 (2368019789 / 4000000000 : ℝ) (74000618407 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1455 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1457 : ℝ := e5 + e1456
lemma b1457 : Encl e1457 (6368019789 / 4000000000 : ℝ) (199000618407 / 125000000000 : ℝ) := by
  exact Encl.add b5 b1456 (by norm_num) (by norm_num)

def e1458 : ℝ := Real.sqrt e1457
lemma b1458 : Encl e1458 (10093974273 / 8000000000 : ℝ) (9857396751 / 7812500000 : ℝ) := by
  exact Encl.sqrt b1457 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1459 : ℝ := e1454 * e1458
lemma b1459 : Encl e1459 (970811415683 / 500000000000 : ℝ) (1941622831377 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1454 b1458 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1460 : ℝ := e97 * e1455
lemma b1460 : Encl e1460 (1184009894501 / 1000000000000 : ℝ) (1184009894511 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1455 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1461 : ℝ := e1459 - e1460
lemma b1461 : Encl e1461 (151522587371 / 200000000000 : ℝ) (189403234219 / 250000000000 : ℝ) := by
  exact Encl.sub b1459 b1460 (by norm_num) (by norm_num)

def e1462 : ℝ := e1395 * e1461
lemma b1462 : Encl e1462 (669301803189 / 1000000000000 : ℝ) (66930180321 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1395 b1461 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1463 : ℝ := e1452 - e1462
lemma b1463 : Encl e1463 (46244218837 / 1000000000000 : ℝ) (46244218883 / 1000000000000 : ℝ) := by
  exact Encl.sub b1452 b1462 (by norm_num) (by norm_num)

def e1464 : ℝ := e165 - e1423
lemma b1464 : Encl e1464 (4437343133 / 20000000000 : ℝ) (110933578361 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b1423 (by norm_num) (by norm_num)

def e1465 : ℝ := e1463 * e1464
lemma b1465 : Encl e1465 (80156823 / 7812500000 : ℝ) (10260073359 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1463 b1464 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1466 : ℝ := e1461 - e1414
lemma b1466 : Encl e1466 (34651732049 / 1000000000000 : ℝ) (17325866047 / 500000000000 : ℝ) := by
  exact Encl.sub b1461 b1414 (by norm_num) (by norm_num)

def e1467 : ℝ := e183 - e1445
lemma b1467 : Encl e1467 (5207191343 / 25000000000 : ℝ) (208287653867 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b1445 (by norm_num) (by norm_num)

def e1468 : ℝ := e1466 * e1467
lemma b1468 : Encl e1468 (1443505593 / 200000000000 : ℝ) (7217527981 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1466 b1467 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1469 : ℝ := e1465 + e1468
lemma b1469 : Encl e1469 (17477601309 / 1000000000000 : ℝ) (873880067 / 50000000000 : ℝ) := by
  exact Encl.add b1465 b1468 (by norm_num) (by norm_num)

def e1470 : ℝ := e4 - e1395
lemma b1470 : Encl e1470 (26577073607 / 250000000000 : ℝ) (106308294431 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b1395 (by norm_num) (by norm_num)

def e1471 : ℝ := e1469 / e1470
lemma b1471 : Encl e1471 (164404869841 / 1000000000000 : ℝ) (82202435069 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1469 b1470 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1472 : ℝ := e1451 + e1471
lemma b1472 : Encl e1472 (-924869053 / 1000000000000 : ℝ) (-115608569 / 125000000000 : ℝ) := by
  exact Encl.add b1451 b1471 (by norm_num) (by norm_num)

def e1473 : ℝ := e924 / e1326
lemma b1473 : Encl e1473 (842105263157 / 1000000000000 : ℝ) (421052631579 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1474 : ℝ := min e7 e1473
lemma b1474 : Encl e1474 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1473 (by norm_num) (by norm_num)

def e1475 : ℝ := e1474 - e5
lemma b1475 : Encl e1475 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1474 b5 (by norm_num) (by norm_num)

def e1476 : ℝ := e23 * e1326
lemma b1476 : Encl e1476 (57 / 25 : ℝ) (57 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1477 : ℝ := e1476 * e1337
lemma b1477 : Encl e1477 (433571244727 / 250000000000 : ℝ) (867142489457 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1476 b1337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1478 : ℝ := e1477 / e0
lemma b1478 : Encl e1478 (276020027123 / 500000000000 : ℝ) (552040054249 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1477 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1479 : ℝ := e1475 + e1478
lemma b1479 : Encl e1479 (116865084031 / 500000000000 : ℝ) (116865084033 / 500000000000 : ℝ) := by
  exact Encl.add b1475 b1478 (by norm_num) (by norm_num)

def e1480 : ℝ := e23 * e1331
lemma b1480 : Encl e1480 (3249 / 1250 : ℝ) (3249 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b1331 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1481 : ℝ := e1480 * e1337
lemma b1481 : Encl e1481 (494271218989 / 250000000000 : ℝ) (988542437981 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1480 b1337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1482 : ℝ := e0 + e1481
lemma b1482 : Encl e1482 (1023735505909 / 200000000000 : ℝ) (319917345597 / 62500000000 : ℝ) := by
  exact Encl.add b0 b1481 (by norm_num) (by norm_num)

def e1483 : ℝ := Real.sqrt e1482
lemma b1483 : Encl e1483 (1131224726739 / 500000000000 : ℝ) (2262449453481 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1482 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1484 : ℝ := e932 * e1483
lemma b1484 : Encl e1484 (288064011213 / 200000000000 : ℝ) (144032005607 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1483 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1485 : ℝ := e1326 ^ 3
lemma b1485 : Encl e1485 (185193 / 125000 : ℝ) (185193 / 125000 : ℝ) := by
  exact Encl.pow b1326 (by norm_num) 3 (by norm_num) (by norm_num)

def e1486 : ℝ := e939 * e1485
lemma b1486 : Encl e1486 (12407931 / 62500000 : ℝ) (12407931 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1485 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1487 : ℝ := min e1486 e941
lemma b1487 : Encl e1487 (12407931 / 62500000 : ℝ) (12407931 / 62500000 : ℝ) := by
  exact Encl.min b1486 b941 (by norm_num) (by norm_num)

def e1488 : ℝ := e23 * e1479
lemma b1488 : Encl e1488 (116865084031 / 250000000000 : ℝ) (116865084033 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1479 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1489 : ℝ := e944 * e1487
lemma b1489 : Encl e1489 (37223793 / 31250000 : ℝ) (37223793 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1487 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1490 : ℝ := e1484 ^ 2
lemma b1490 : Encl e1490 (2074521863903 / 1000000000000 : ℝ) (1037260931959 / 500000000000 : ℝ) := by
  exact Encl.pow b1484 (by norm_num) 2 (by norm_num) (by norm_num)

def e1491 : ℝ := e1489 * e1490
lemma b1491 : Encl e1491 (617772579487 / 250000000000 : ℝ) (2471090317967 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1489 b1490 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1492 : ℝ := e1491 * e1479
lemma b1492 : Encl e1492 (57756835531 / 100000000000 : ℝ) (23102734213 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b1491 b1479 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1493 : ℝ := e1492 / e9
lemma b1493 : Encl e1493 (2062744126107 / 1000000000000 : ℝ) (2062744126161 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1492 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1494 : ℝ := e5 + e1493
lemma b1494 : Encl e1494 (3062744126107 / 1000000000000 : ℝ) (3062744126161 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1493 (by norm_num) (by norm_num)

def e1495 : ℝ := Real.sqrt e1494
lemma b1495 : Encl e1495 (875034874463 / 500000000000 : ℝ) (875034874471 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1494 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1496 : ℝ := e5 + e1495
lemma b1496 : Encl e1496 (1375034874463 / 500000000000 : ℝ) (1375034874471 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1495 (by norm_num) (by norm_num)

def e1497 : ℝ := e1488 / e1496
lemma b1497 : Encl e1497 (84990632747 / 500000000000 : ℝ) (169981265499 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1488 b1496 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1498 : ℝ := e1487 * e954
lemma b1498 : Encl e1498 (1838557583 / 1000000000000 : ℝ) (114909849 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b1487 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1499 : ℝ := e1479 - e1497
lemma b1499 : Encl e1499 (63748902563 / 1000000000000 : ℝ) (15937225643 / 250000000000 : ℝ) := by
  exact Encl.sub b1479 b1497 (by norm_num) (by norm_num)

def e1500 : ℝ := e1499 / e1484
lemma b1500 : Encl e1500 (44260233893 / 1000000000000 : ℝ) (442602339 / 10000000000 : ℝ) := by
  exact Encl.div_nonneg b1499 b1484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1501 : ℝ := e1500 ^ 2
lemma b1501 : Encl e1501 (122435519 / 62500000000 : ℝ) (391793661 / 200000000000 : ℝ) := by
  exact Encl.pow b1500 (by norm_num) 2 (by norm_num) (by norm_num)

def e1502 : ℝ := e9 * e1501
lemma b1502 : Encl e1502 (4388089 / 8000000000 : ℝ) (274255563 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1501 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1503 : ℝ := e1497 ^ 3
lemma b1503 : Encl e1503 (4911375897 / 1000000000000 : ℝ) (2455687949 / 500000000000 : ℝ) := by
  exact Encl.pow b1497 (by norm_num) 3 (by norm_num) (by norm_num)

def e1504 : ℝ := e1487 * e1503
lemma b1504 : Encl e1504 (975040211 / 1000000000000 : ℝ) (975040213 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1487 b1503 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1505 : ℝ := e1502 + e1504
lemma b1505 : Encl e1505 (190443917 / 125000000000 : ℝ) (1523551339 / 1000000000000 : ℝ) := by
  exact Encl.add b1502 b1504 (by norm_num) (by norm_num)

def e1506 : ℝ := min e1498 e1505
lemma b1506 : Encl e1506 (190443917 / 125000000000 : ℝ) (1523551339 / 1000000000000 : ℝ) := by
  exact Encl.min b1498 b1505 (by norm_num) (by norm_num)

def e1507 : ℝ := (59 / 50 : ℝ)
lemma b1507 : Encl e1507 (59 / 50 : ℝ) (59 / 50 : ℝ) := by
  exact Encl.exact (59 / 50 : ℝ)

def e1508 : ℝ := e1507 / e0
lemma b1508 : Encl e1508 (11737677053 / 31250000000 : ℝ) (375605665697 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1507 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1509 : ℝ := e1507 * e7
lemma b1509 : Encl e1509 (402197167151 / 500000000000 : ℝ) (160878866861 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1507 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1510 : ℝ := e8 * e1507
lemma b1510 : Encl e1510 (2891 / 2500 : ℝ) (2891 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1511 : ℝ := e1510 / e0
lemma b1511 : Encl e1511 (184046776191 / 500000000000 : ℝ) (368093552383 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1510 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1512 : ℝ := e1507 ^ 2
lemma b1512 : Encl e1512 (3481 / 2500 : ℝ) (3481 / 2500 : ℝ) := by
  exact Encl.pow b1507 (by norm_num) 2 (by norm_num) (by norm_num)

def e1513 : ℝ := e17 * e1512
lemma b1513 : Encl e1513 (3481 / 625 : ℝ) (3481 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b1512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1514 : ℝ := e1513 / e0
lemma b1514 : Encl e1514 (1772858742089 / 1000000000000 : ℝ) (177285874209 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1513 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1515 : ℝ := e5 + e1514
lemma b1515 : Encl e1515 (2772858742089 / 1000000000000 : ℝ) (277285874209 / 100000000000 : ℝ) := by
  exact Encl.add b5 b1514 (by norm_num) (by norm_num)

def e1516 : ℝ := Real.sqrt e1515
lemma b1516 : Encl e1516 (104074393879 / 62500000000 : ℝ) (333038060413 / 200000000000 : ℝ) := by
  exact Encl.sqrt b1515 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1517 : ℝ := e5 + e1516
lemma b1517 : Encl e1517 (166574393879 / 62500000000 : ℝ) (533038060413 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1516 (by norm_num) (by norm_num)

def e1518 : ℝ := e23 / e1517
lemma b1518 : Encl e1518 (187603864389 / 250000000000 : ℝ) (375207728779 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1517 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1519 : ℝ := e9 * e1518
lemma b1519 : Encl e1519 (42023265623 / 200000000000 : ℝ) (210116328117 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1520 : ℝ := e1511 + e1519
lemma b1520 : Encl e1520 (578209880497 / 1000000000000 : ℝ) (1156419761 / 2000000000 : ℝ) := by
  exact Encl.add b1511 b1519 (by norm_num) (by norm_num)

def e1521 : ℝ := e1520 - e5
lemma b1521 : Encl e1521 (-421790119503 / 1000000000000 : ℝ) (-843580239 / 2000000000 : ℝ) := by
  exact Encl.sub b1520 b5 (by norm_num) (by norm_num)

def e1522 : ℝ := e0 / e1512
lemma b1522 : Encl e1522 (2256242928461 / 1000000000000 : ℝ) (1128121464231 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1523 : ℝ := e1508 ^ 2
lemma b1523 : Encl e1523 (70539808051 / 500000000000 : ℝ) (17634952013 / 125000000000 : ℝ) := by
  exact Encl.pow b1508 (by norm_num) 2 (by norm_num) (by norm_num)

def e1524 : ℝ := e5 - e1523
lemma b1524 : Encl e1524 (107365047987 / 125000000000 : ℝ) (429460191949 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1523 (by norm_num) (by norm_num)

def e1525 : ℝ := Real.sqrt e1524
lemma b1525 : Encl e1525 (463389788379 / 500000000000 : ℝ) (23169489419 / 25000000000 : ℝ) := by
  exact Encl.sqrt b1524 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1526 : ℝ := e29 - e1525
lemma b1526 : Encl e1526 (-130056455047 / 500000000000 : ℝ) (-260112910091 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b1525 (by norm_num) (by norm_num)

def e1527 : ℝ := e1525 ^ 3
lemma b1527 : Encl e1527 (159205973971 / 200000000000 : ℝ) (796029869861 / 1000000000000 : ℝ) := by
  exact Encl.pow b1525 (by norm_num) 3 (by norm_num) (by norm_num)

def e1528 : ℝ := e1527 / e35
lemma b1528 : Encl e1528 (265343289951 / 1000000000000 : ℝ) (132671644977 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1527 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1529 : ℝ := e1526 + e1528
lemma b1529 : Encl e1529 (5230379857 / 1000000000000 : ℝ) (5230379863 / 1000000000000 : ℝ) := by
  exact Encl.add b1526 b1528 (by norm_num) (by norm_num)

def e1530 : ℝ := e8 * e1529
lemma b1530 : Encl e1530 (5125772259 / 1000000000000 : ℝ) (2562886133 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1529 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1531 : ℝ := e1523 / e1525
lemma b1531 : Encl e1531 (3805641051 / 25000000000 : ℝ) (152225642043 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1523 b1525 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1532 : ℝ := e1531 - e23
lemma b1532 : Encl e1532 (-46194358949 / 25000000000 : ℝ) (-1847774357957 / 1000000000000 : ℝ) := by
  exact Encl.sub b1531 b23 (by norm_num) (by norm_num)

def e1533 : ℝ := e23 * e1525
lemma b1533 : Encl e1533 (463389788379 / 250000000000 : ℝ) (23169489419 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1525 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1534 : ℝ := e1532 + e1533
lemma b1534 : Encl e1534 (1446198889 / 250000000000 : ℝ) (5784795563 / 1000000000000 : ℝ) := by
  exact Encl.add b1532 b1533 (by norm_num) (by norm_num)

def e1535 : ℝ := e1534 / e43
lemma b1535 : Encl e1535 (115695911 / 1000000000000 : ℝ) (14461989 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1534 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1536 : ℝ := e1530 - e1535
lemma b1536 : Encl e1536 (5010076347 / 1000000000000 : ℝ) (1002015271 / 200000000000 : ℝ) := by
  exact Encl.sub b1530 b1535 (by norm_num) (by norm_num)

def e1537 : ℝ := e1522 * e1536
lemma b1537 : Encl e1537 (706496833 / 62500000000 : ℝ) (2825987337 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1522 b1536 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1538 : ℝ := e1521 + e1537
lemma b1538 : Encl e1538 (-16419446807 / 40000000000 : ℝ) (-51310771269 / 125000000000 : ℝ) := by
  exact Encl.add b1521 b1537 (by norm_num) (by norm_num)

def e1539 : ℝ := e1509 ^ 2
lemma b1539 : Encl e1539 (647050245057 / 1000000000000 : ℝ) (323525122531 / 500000000000 : ℝ) := by
  exact Encl.pow b1509 (by norm_num) 2 (by norm_num) (by norm_num)

def e1540 : ℝ := e5 - e1539
lemma b1540 : Encl e1540 (176474877469 / 500000000000 : ℝ) (352949754943 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1539 (by norm_num) (by norm_num)

def e1541 : ℝ := Real.sqrt e1540
lemma b1541 : Encl e1541 (297047872799 / 500000000000 : ℝ) (594095745603 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1540 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1542 : ℝ := e5 + e1541
lemma b1542 : Encl e1542 (797047872799 / 500000000000 : ℝ) (1594095745603 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1541 (by norm_num) (by norm_num)

def e1543 : ℝ := e1509 / e1542
lemma b1543 : Encl e1543 (5046085447 / 10000000000 : ℝ) (7884508511 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b1509 b1542 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1544 : ℝ := e1543 ^ 2
lemma b1544 : Encl e1544 (31828722923 / 125000000000 : ℝ) (254629783389 / 1000000000000 : ℝ) := by
  exact Encl.pow b1543 (by norm_num) 2 (by norm_num) (by norm_num)

def e1545 : ℝ := e5 + e1544
lemma b1545 : Encl e1545 (156828722923 / 125000000000 : ℝ) (1254629783389 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1544 (by norm_num) (by norm_num)

def e1546 : ℝ := Real.sqrt e1545
lemma b1546 : Encl e1546 (112010257717 / 100000000000 : ℝ) (1120102577173 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1545 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1547 : ℝ := e5 + e1546
lemma b1547 : Encl e1547 (212010257717 / 100000000000 : ℝ) (2120102577173 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1546 (by norm_num) (by norm_num)

def e1548 : ℝ := e1543 / e1547
lemma b1548 : Encl e1548 (238011382153 / 1000000000000 : ℝ) (59502845539 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1543 b1547 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1549 : ℝ := Real.arcsin e1509
lemma b1549 : Encl e1549 (467327644273 / 500000000000 : ℝ) (934655288559 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e1509) (a := (238011382153 / 1000000000000 : ℝ)) (b := (59502845539 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (402197167151 / 500000000000 : ℝ) by norm_num).trans b1509.1
        exact b1509.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1509) (238011382153 / 1000000000000 : ℝ) (59502845539 / 250000000000 : ℝ) from b1548) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1550 : ℝ := e59 * e1549
lemma b1550 : Encl e1550 (238337098579 / 500000000000 : ℝ) (238337098583 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1549 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1551 : ℝ := e61 * e1509
lemma b1551 : Encl e1551 (394153223807 / 1000000000000 : ℝ) (39415322381 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1509 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1552 : ℝ := e1551 * e1541
lemma b1552 : Encl e1552 (234164753377 / 1000000000000 : ℝ) (117082376691 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1551 b1541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1553 : ℝ := e1550 - e1552
lemma b1553 : Encl e1553 (3789210059 / 15625000000 : ℝ) (242509443789 / 1000000000000 : ℝ) := by
  exact Encl.sub b1550 b1552 (by norm_num) (by norm_num)

def e1554 : ℝ := e43 * e1541
lemma b1554 : Encl e1554 (297047872799 / 10000000000 : ℝ) (594095745603 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1555 : ℝ := e1509 / e1554
lemma b1555 : Encl e1555 (27079619413 / 1000000000000 : ℝ) (13539809707 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1509 b1554 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1556 : ℝ := e1553 - e1555
lemma b1556 : Encl e1556 (107714912181 / 500000000000 : ℝ) (26928728047 / 125000000000 : ℝ) := by
  exact Encl.sub b1553 b1555 (by norm_num) (by norm_num)

def e1557 : ℝ := e5 + e1525
lemma b1557 : Encl e1557 (963389788379 / 500000000000 : ℝ) (48169489419 / 25000000000 : ℝ) := by
  exact Encl.add b5 b1525 (by norm_num) (by norm_num)

def e1558 : ℝ := e1508 / e1557
lemma b1558 : Encl e1558 (38987922669 / 200000000000 : ℝ) (194939613347 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1508 b1557 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1559 : ℝ := e1558 ^ 2
lemma b1559 : Encl e1559 (38001452851 / 1000000000000 : ℝ) (9500363213 / 250000000000 : ℝ) := by
  exact Encl.pow b1558 (by norm_num) 2 (by norm_num) (by norm_num)

def e1560 : ℝ := e5 + e1559
lemma b1560 : Encl e1560 (1038001452851 / 1000000000000 : ℝ) (259500363213 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1559 (by norm_num) (by norm_num)

def e1561 : ℝ := Real.sqrt e1560
lemma b1561 : Encl e1561 (25470589079 / 25000000000 : ℝ) (1018823563161 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1560 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1562 : ℝ := e5 + e1561
lemma b1562 : Encl e1562 (50470589079 / 25000000000 : ℝ) (2018823563161 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1561 (by norm_num) (by norm_num)

def e1563 : ℝ := e1558 / e1562
lemma b1563 : Encl e1563 (12070124459 / 125000000000 : ℝ) (48280497837 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1558 b1562 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1564 : ℝ := Real.arcsin e1508
lemma b1564 : Encl e1564 (77010040893 / 200000000000 : ℝ) (192525102237 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e1508) (a := (12070124459 / 125000000000 : ℝ)) (b := (48280497837 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (11737677053 / 31250000000 : ℝ) by norm_num).trans b1508.1
        exact b1508.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1508) (12070124459 / 125000000000 : ℝ) (48280497837 / 500000000000 : ℝ) from b1563) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1565 : ℝ := e59 * e1564
lemma b1565 : Encl e1565 (196375604277 / 1000000000000 : ℝ) (98187802141 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1564 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1566 : ℝ := e61 * e1508
lemma b1566 : Encl e1566 (184046776191 / 1000000000000 : ℝ) (1437865439 / 7812500000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1508 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1567 : ℝ := e1566 * e1525
lemma b1567 : Encl e1567 (170570793341 / 1000000000000 : ℝ) (1332584323 / 7812500000 : ℝ) := by
  exact Encl.mul_nonneg b1566 b1525 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1568 : ℝ := e1565 - e1567
lemma b1568 : Encl e1568 (25804810933 / 1000000000000 : ℝ) (25804810941 / 1000000000000 : ℝ) := by
  exact Encl.sub b1565 b1567 (by norm_num) (by norm_num)

def e1569 : ℝ := e43 * e1525
lemma b1569 : Encl e1569 (463389788379 / 10000000000 : ℝ) (23169489419 / 500000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1525 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1570 : ℝ := e1508 / e1569
lemma b1570 : Encl e1570 (8105609469 / 1000000000000 : ℝ) (810560947 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1508 b1569 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1571 : ℝ := e1568 - e1570
lemma b1571 : Encl e1571 (17699201463 / 1000000000000 : ℝ) (276550023 / 15625000000 : ℝ) := by
  exact Encl.sub b1568 b1570 (by norm_num) (by norm_num)

def e1572 : ℝ := e1556 - e1571
lemma b1572 : Encl e1572 (19773062289 / 100000000000 : ℝ) (197730622913 / 1000000000000 : ℝ) := by
  exact Encl.sub b1556 b1571 (by norm_num) (by norm_num)

def e1573 : ℝ := e1572 / e1507
lemma b1573 : Encl e1573 (167568324483 / 1000000000000 : ℝ) (167568324503 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1572 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1574 : ℝ := e1538 + e1573
lemma b1574 : Encl e1574 (-60729461423 / 250000000000 : ℝ) (-242917845649 / 1000000000000 : ℝ) := by
  exact Encl.add b1538 b1573 (by norm_num) (by norm_num)

def e1575 : ℝ := e1509 + e4
lemma b1575 : Encl e1575 (112133603307 / 62500000000 : ℝ) (448534413229 / 250000000000 : ℝ) := by
  exact Encl.add b1509 b4 (by norm_num) (by norm_num)

def e1576 : ℝ := e1575 / e23
lemma b1576 : Encl e1576 (112133603307 / 125000000000 : ℝ) (448534413229 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1575 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1577 : ℝ := e1509 / e1507
lemma b1577 : Encl e1577 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1509 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1578 : ℝ := e89 * e1577
lemma b1578 : Encl e1578 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1577 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1579 : ℝ := e1577 ^ 2
lemma b1579 : Encl e1579 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1577 (by norm_num) 2 (by norm_num) (by norm_num)

def e1580 : ℝ := e91 * e1579
lemma b1580 : Encl e1580 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1581 : ℝ := e5 + e1580
lemma b1581 : Encl e1581 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1580 (by norm_num) (by norm_num)

def e1582 : ℝ := Real.sqrt e1581
lemma b1582 : Encl e1582 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1581 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1583 : ℝ := e1578 * e1582
lemma b1583 : Encl e1583 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1578 b1582 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1584 : ℝ := e97 * e1579
lemma b1584 : Encl e1584 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1585 : ℝ := e1583 - e1584
lemma b1585 : Encl e1585 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1583 b1584 (by norm_num) (by norm_num)

def e1586 : ℝ := e1576 * e1585
lemma b1586 : Encl e1586 (611522950397 / 1000000000000 : ℝ) (30576147521 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b1576 b1585 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1587 : ℝ := e1576 / e1507
lemma b1587 : Encl e1587 (76022781903 / 100000000000 : ℝ) (760227819033 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1576 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1588 : ℝ := e89 * e1587
lemma b1588 : Encl e1588 (336867181351 / 250000000000 : ℝ) (1347468725411 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1587 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1589 : ℝ := e1587 ^ 2
lemma b1589 : Encl e1589 (577946336827 / 1000000000000 : ℝ) (9030411513 / 15625000000 : ℝ) := by
  exact Encl.pow b1587 (by norm_num) 2 (by norm_num) (by norm_num)

def e1590 : ℝ := e91 * e1589
lemma b1590 : Encl e1590 (90783598297 / 200000000000 : ℝ) (453917991491 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1589 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1591 : ℝ := e5 + e1590
lemma b1591 : Encl e1591 (290783598297 / 200000000000 : ℝ) (1453917991491 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1590 (by norm_num) (by norm_num)

def e1592 : ℝ := Real.sqrt e1591
lemma b1592 : Encl e1592 (75361576113 / 62500000000 : ℝ) (1205785217811 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1591 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1593 : ℝ := e1588 * e1592
lemma b1593 : Encl e1593 (32495157411 / 20000000000 : ℝ) (406189467641 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1588 b1592 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1594 : ℝ := e97 * e1589
lemma b1594 : Encl e1594 (907835982971 / 1000000000000 : ℝ) (907835982981 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1589 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1595 : ℝ := e1593 - e1594
lemma b1595 : Encl e1595 (716921887569 / 1000000000000 : ℝ) (716921887593 / 1000000000000 : ℝ) := by
  exact Encl.sub b1593 b1594 (by norm_num) (by norm_num)

def e1596 : ℝ := e1509 * e1595
lemma b1596 : Encl e1596 (576687904497 / 1000000000000 : ℝ) (14417197613 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b1509 b1595 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1597 : ℝ := e1586 - e1596
lemma b1597 : Encl e1597 (34835045877 / 1000000000000 : ℝ) (34835045923 / 1000000000000 : ℝ) := by
  exact Encl.sub b1586 b1596 (by norm_num) (by norm_num)

def e1598 : ℝ := e1576 ^ 2
lemma b1598 : Encl e1598 (804732479399 / 1000000000000 : ℝ) (804732479403 / 1000000000000 : ℝ) := by
  exact Encl.pow b1576 (by norm_num) 2 (by norm_num) (by norm_num)

def e1599 : ℝ := e8 * e1598
lemma b1599 : Encl e1599 (788637829811 / 1000000000000 : ℝ) (157727565963 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1598 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1600 : ℝ := e5 - e1599
lemma b1600 : Encl e1600 (42272434037 / 200000000000 : ℝ) (211362170189 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1599 (by norm_num) (by norm_num)

def e1601 : ℝ := e5 - e1598
lemma b1601 : Encl e1601 (195267520597 / 1000000000000 : ℝ) (195267520601 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1598 (by norm_num) (by norm_num)

def e1602 : ℝ := Real.sqrt e1601

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
