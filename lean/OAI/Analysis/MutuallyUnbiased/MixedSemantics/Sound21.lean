import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons21

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1344 node1344Labels = Sparse.eval nodeValue1344 (mixedVector B) := by
  have h := singleton1344 B _hB
  rw [sound69 B _hB _hF] at h
  norm_num [nodeValue1344, nodeValue69, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1345 node1345Labels = Sparse.eval nodeValue1345 (mixedVector B) := by
  simpa only [nodeValue1345, Sparse.eval_nil] using zero1345 B _hB _hF

theorem sound1346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1346 node1346Labels = Sparse.eval nodeValue1346 (mixedVector B) := by
  have h := singleton1346 B _hB
  rw [sound62 B _hB _hF] at h
  norm_num [nodeValue1346, nodeValue62, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1347 node1347Labels = Sparse.eval nodeValue1347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1347) = mixedMoment B node1347 node1347Labels := rfl
  simpa [nodeValue1347, Sparse.eval] using hc.symm

theorem sound1348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1348 node1348Labels = Sparse.eval nodeValue1348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1348) = mixedMoment B node1348 node1348Labels := rfl
  simpa [nodeValue1348, Sparse.eval] using hc.symm

theorem sound1349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1349 node1349Labels = Sparse.eval nodeValue1349 (mixedVector B) := by
  have h := singleton1349 B _hB
  rw [sound71 B _hB _hF] at h
  norm_num [nodeValue1349, nodeValue71, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1350 node1350Labels = Sparse.eval nodeValue1350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1350) = mixedMoment B node1350 node1350Labels := rfl
  simpa [nodeValue1350, Sparse.eval] using hc.symm

theorem sound1351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1351 node1351Labels = Sparse.eval nodeValue1351 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1351) = mixedMoment B node1351 node1351Labels := rfl
  simpa [nodeValue1351, Sparse.eval] using hc.symm

theorem sound1352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1352 node1352Labels = Sparse.eval nodeValue1352 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1352) = mixedMoment B node1352 node1352Labels := rfl
  simpa [nodeValue1352, Sparse.eval] using hc.symm

theorem sound1353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1353 node1353Labels = Sparse.eval nodeValue1353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1353) = mixedMoment B node1353 node1353Labels := rfl
  simpa [nodeValue1353, Sparse.eval] using hc.symm

theorem sound1354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1354 node1354Labels = Sparse.eval nodeValue1354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1354) = mixedMoment B node1354 node1354Labels := rfl
  simpa [nodeValue1354, Sparse.eval] using hc.symm

theorem sound1355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1355 node1355Labels = Sparse.eval nodeValue1355 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1355) = mixedMoment B node1355 node1355Labels := rfl
  simpa [nodeValue1355, Sparse.eval] using hc.symm

theorem sound1356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1356 node1356Labels = Sparse.eval nodeValue1356 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1356) = mixedMoment B node1356 node1356Labels := rfl
  simpa [nodeValue1356, Sparse.eval] using hc.symm

theorem sound1357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1357 node1357Labels = Sparse.eval nodeValue1357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1357) = mixedMoment B node1357 node1357Labels := rfl
  simpa [nodeValue1357, Sparse.eval] using hc.symm

theorem sound1358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1358 node1358Labels = Sparse.eval nodeValue1358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1358) = mixedMoment B node1358 node1358Labels := rfl
  simpa [nodeValue1358, Sparse.eval] using hc.symm

theorem sound1359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1359 node1359Labels = Sparse.eval nodeValue1359 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1359) = mixedMoment B node1359 node1359Labels := rfl
  simpa [nodeValue1359, Sparse.eval] using hc.symm

theorem sound1360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1360 node1360Labels = Sparse.eval nodeValue1360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1360) = mixedMoment B node1360 node1360Labels := rfl
  simpa [nodeValue1360, Sparse.eval] using hc.symm

theorem sound1361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1361 node1361Labels = Sparse.eval nodeValue1361 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1361) = mixedMoment B node1361 node1361Labels := rfl
  simpa [nodeValue1361, Sparse.eval] using hc.symm

theorem sound1362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1362 node1362Labels = Sparse.eval nodeValue1362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1362) = mixedMoment B node1362 node1362Labels := rfl
  simpa [nodeValue1362, Sparse.eval] using hc.symm

theorem sound1363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1363 node1363Labels = Sparse.eval nodeValue1363 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1363) = mixedMoment B node1363 node1363Labels := rfl
  simpa [nodeValue1363, Sparse.eval] using hc.symm

theorem sound1364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1364 node1364Labels = Sparse.eval nodeValue1364 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1364) = mixedMoment B node1364 node1364Labels := rfl
  simpa [nodeValue1364, Sparse.eval] using hc.symm

theorem sound1365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1365 node1365Labels = Sparse.eval nodeValue1365 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1365) = mixedMoment B node1365 node1365Labels := rfl
  simpa [nodeValue1365, Sparse.eval] using hc.symm

theorem sound1366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1366 node1366Labels = Sparse.eval nodeValue1366 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1366) = mixedMoment B node1366 node1366Labels := rfl
  simpa [nodeValue1366, Sparse.eval] using hc.symm

theorem sound1367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1367 node1367Labels = Sparse.eval nodeValue1367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1367) = mixedMoment B node1367 node1367Labels := rfl
  simpa [nodeValue1367, Sparse.eval] using hc.symm

theorem sound1368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1368 node1368Labels = Sparse.eval nodeValue1368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1368) = mixedMoment B node1368 node1368Labels := rfl
  simpa [nodeValue1368, Sparse.eval] using hc.symm

theorem sound1369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1369 node1369Labels = Sparse.eval nodeValue1369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1369) = mixedMoment B node1369 node1369Labels := rfl
  simpa [nodeValue1369, Sparse.eval] using hc.symm

theorem sound1370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1370 node1370Labels = Sparse.eval nodeValue1370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1370) = mixedMoment B node1370 node1370Labels := rfl
  simpa [nodeValue1370, Sparse.eval] using hc.symm

theorem sound1371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1371 node1371Labels = Sparse.eval nodeValue1371 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1371) = mixedMoment B node1371 node1371Labels := rfl
  simpa [nodeValue1371, Sparse.eval] using hc.symm

theorem sound1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1372 node1372Labels = Sparse.eval nodeValue1372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1372) = mixedMoment B node1372 node1372Labels := rfl
  simpa [nodeValue1372, Sparse.eval] using hc.symm

theorem sound1373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1373 node1373Labels = Sparse.eval nodeValue1373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1373) = mixedMoment B node1373 node1373Labels := rfl
  simpa [nodeValue1373, Sparse.eval] using hc.symm

theorem sound1374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1374 node1374Labels = Sparse.eval nodeValue1374 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1374) = mixedMoment B node1374 node1374Labels := rfl
  simpa [nodeValue1374, Sparse.eval] using hc.symm

theorem sound1375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1375 node1375Labels = Sparse.eval nodeValue1375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1375) = mixedMoment B node1375 node1375Labels := rfl
  simpa [nodeValue1375, Sparse.eval] using hc.symm

theorem sound1376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1376 node1376Labels = Sparse.eval nodeValue1376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1376) = mixedMoment B node1376 node1376Labels := rfl
  simpa [nodeValue1376, Sparse.eval] using hc.symm

theorem sound1377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1377 node1377Labels = Sparse.eval nodeValue1377 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1377) = mixedMoment B node1377 node1377Labels := rfl
  simpa [nodeValue1377, Sparse.eval] using hc.symm

theorem sound1378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1378 node1378Labels = Sparse.eval nodeValue1378 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1378) = mixedMoment B node1378 node1378Labels := rfl
  simpa [nodeValue1378, Sparse.eval] using hc.symm

theorem sound1379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1379 node1379Labels = Sparse.eval nodeValue1379 (mixedVector B) := by
  simpa only [nodeValue1379, Sparse.eval_nil] using zero1379 B _hB _hF

theorem sound1380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1380 node1380Labels = Sparse.eval nodeValue1380 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1380) = mixedMoment B node1380 node1380Labels := rfl
  simpa [nodeValue1380, Sparse.eval] using hc.symm

theorem sound1381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1381 node1381Labels = Sparse.eval nodeValue1381 (mixedVector B) := by
  simpa only [nodeValue1381, Sparse.eval_nil] using zero1381 B _hB _hF

theorem sound1382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1382 node1382Labels = Sparse.eval nodeValue1382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1382) = mixedMoment B node1382 node1382Labels := rfl
  simpa [nodeValue1382, Sparse.eval] using hc.symm

theorem sound1383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1383 node1383Labels = Sparse.eval nodeValue1383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1383) = mixedMoment B node1383 node1383Labels := rfl
  simpa [nodeValue1383, Sparse.eval] using hc.symm

theorem sound1384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1384 node1384Labels = Sparse.eval nodeValue1384 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1384) = mixedMoment B node1384 node1384Labels := rfl
  simpa [nodeValue1384, Sparse.eval] using hc.symm

theorem sound1385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1385 node1385Labels = Sparse.eval nodeValue1385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1385) = mixedMoment B node1385 node1385Labels := rfl
  simpa [nodeValue1385, Sparse.eval] using hc.symm

theorem sound1386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1386 node1386Labels = Sparse.eval nodeValue1386 (mixedVector B) := by
  simpa only [nodeValue1386, Sparse.eval_nil] using zero1386 B _hB _hF

theorem sound1387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1387 node1387Labels = Sparse.eval nodeValue1387 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1387) = mixedMoment B node1387 node1387Labels := rfl
  simpa [nodeValue1387, Sparse.eval] using hc.symm

theorem sound1388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1388 node1388Labels = Sparse.eval nodeValue1388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1388) = mixedMoment B node1388 node1388Labels := rfl
  simpa [nodeValue1388, Sparse.eval] using hc.symm

theorem sound1389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1389 node1389Labels = Sparse.eval nodeValue1389 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1389) = mixedMoment B node1389 node1389Labels := rfl
  simpa [nodeValue1389, Sparse.eval] using hc.symm

theorem sound1390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1390 node1390Labels = Sparse.eval nodeValue1390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1390) = mixedMoment B node1390 node1390Labels := rfl
  simpa [nodeValue1390, Sparse.eval] using hc.symm

theorem sound1391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1391 node1391Labels = Sparse.eval nodeValue1391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1391) = mixedMoment B node1391 node1391Labels := rfl
  simpa [nodeValue1391, Sparse.eval] using hc.symm

theorem sound1392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1392 node1392Labels = Sparse.eval nodeValue1392 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1392) = mixedMoment B node1392 node1392Labels := rfl
  simpa [nodeValue1392, Sparse.eval] using hc.symm

theorem sound1393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1393 node1393Labels = Sparse.eval nodeValue1393 (mixedVector B) := by
  simpa only [nodeValue1393, Sparse.eval_nil] using zero1393 B _hB _hF

theorem sound1394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1394 node1394Labels = Sparse.eval nodeValue1394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1394) = mixedMoment B node1394 node1394Labels := rfl
  simpa [nodeValue1394, Sparse.eval] using hc.symm

theorem sound1395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1395 node1395Labels = Sparse.eval nodeValue1395 (mixedVector B) := by
  have h := singleton1395 B _hB
  rw [sound79 B _hB _hF] at h
  norm_num [nodeValue1395, nodeValue79, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1396 node1396Labels = Sparse.eval nodeValue1396 (mixedVector B) := by
  have h := singleton1396 B _hB
  rw [sound77 B _hB _hF] at h
  norm_num [nodeValue1396, nodeValue77, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1397 node1397Labels = Sparse.eval nodeValue1397 (mixedVector B) := by
  have h := singleton1397 B _hB
  rw [sound80 B _hB _hF] at h
  norm_num [nodeValue1397, nodeValue80, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1398 node1398Labels = Sparse.eval nodeValue1398 (mixedVector B) := by
  simpa only [nodeValue1398, Sparse.eval_nil] using zero1398 B _hB _hF

theorem sound1399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1399 node1399Labels = Sparse.eval nodeValue1399 (mixedVector B) := by
  have h := singleton1399 B _hB
  rw [sound78 B _hB _hF] at h
  norm_num [nodeValue1399, nodeValue78, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1400 node1400Labels = Sparse.eval nodeValue1400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1400) = mixedMoment B node1400 node1400Labels := rfl
  simpa [nodeValue1400, Sparse.eval] using hc.symm

theorem sound1401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1401 node1401Labels = Sparse.eval nodeValue1401 (mixedVector B) := by
  have h := singleton1401 B _hB
  rw [sound81 B _hB _hF] at h
  norm_num [nodeValue1401, nodeValue81, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1402 node1402Labels = Sparse.eval nodeValue1402 (mixedVector B) := by
  have h := singleton1402 B _hB
  rw [sound82 B _hB _hF] at h
  norm_num [nodeValue1402, nodeValue82, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1403 node1403Labels = Sparse.eval nodeValue1403 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1403) = mixedMoment B node1403 node1403Labels := rfl
  simpa [nodeValue1403, Sparse.eval] using hc.symm

theorem sound1404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1404 node1404Labels = Sparse.eval nodeValue1404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1404) = mixedMoment B node1404 node1404Labels := rfl
  simpa [nodeValue1404, Sparse.eval] using hc.symm

theorem sound1405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1405 node1405Labels = Sparse.eval nodeValue1405 (mixedVector B) := by
  simpa only [nodeValue1405, Sparse.eval_nil] using zero1405 B _hB _hF

theorem sound1406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1406 node1406Labels = Sparse.eval nodeValue1406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1406) = mixedMoment B node1406 node1406Labels := rfl
  simpa [nodeValue1406, Sparse.eval] using hc.symm

theorem sound1407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1407 node1407Labels = Sparse.eval nodeValue1407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1407) = mixedMoment B node1407 node1407Labels := rfl
  simpa [nodeValue1407, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
