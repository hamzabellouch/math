import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons22

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1408 node1408Labels = Sparse.eval nodeValue1408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1408) = mixedMoment B node1408 node1408Labels := rfl
  simpa [nodeValue1408, Sparse.eval] using hc.symm

theorem sound1409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1409 node1409Labels = Sparse.eval nodeValue1409 (mixedVector B) := by
  have h := singleton1409 B _hB
  rw [sound91 B _hB _hF] at h
  norm_num [nodeValue1409, nodeValue91, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1410 node1410Labels = Sparse.eval nodeValue1410 (mixedVector B) := by
  have h := singleton1410 B _hB
  rw [sound95 B _hB _hF] at h
  norm_num [nodeValue1410, nodeValue95, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1411 node1411Labels = Sparse.eval nodeValue1411 (mixedVector B) := by
  have h := singleton1411 B _hB
  rw [sound93 B _hB _hF] at h
  norm_num [nodeValue1411, nodeValue93, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1412 node1412Labels = Sparse.eval nodeValue1412 (mixedVector B) := by
  have h := singleton1412 B _hB
  rw [sound89 B _hB _hF] at h
  norm_num [nodeValue1412, nodeValue89, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1413 node1413Labels = Sparse.eval nodeValue1413 (mixedVector B) := by
  have h := singleton1413 B _hB
  rw [sound96 B _hB _hF] at h
  norm_num [nodeValue1413, nodeValue96, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1414 node1414Labels = Sparse.eval nodeValue1414 (mixedVector B) := by
  have h := singleton1414 B _hB
  rw [sound92 B _hB _hF] at h
  norm_num [nodeValue1414, nodeValue92, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1415 node1415Labels = Sparse.eval nodeValue1415 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1415) = mixedMoment B node1415 node1415Labels := rfl
  simpa [nodeValue1415, Sparse.eval] using hc.symm

theorem sound1416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1416 node1416Labels = Sparse.eval nodeValue1416 (mixedVector B) := by
  have h := singleton1416 B _hB
  rw [sound94 B _hB _hF] at h
  norm_num [nodeValue1416, nodeValue94, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1417 node1417Labels = Sparse.eval nodeValue1417 (mixedVector B) := by
  have h := singleton1417 B _hB
  rw [sound90 B _hB _hF] at h
  norm_num [nodeValue1417, nodeValue90, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1418 node1418Labels = Sparse.eval nodeValue1418 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1418) = mixedMoment B node1418 node1418Labels := rfl
  simpa [nodeValue1418, Sparse.eval] using hc.symm

theorem sound1419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1419 node1419Labels = Sparse.eval nodeValue1419 (mixedVector B) := by
  have h := singleton1419 B _hB
  rw [sound98 B _hB _hF] at h
  norm_num [nodeValue1419, nodeValue98, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1420 node1420Labels = Sparse.eval nodeValue1420 (mixedVector B) := by
  have h := singleton1420 B _hB
  rw [sound99 B _hB _hF] at h
  norm_num [nodeValue1420, nodeValue99, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1421 node1421Labels = Sparse.eval nodeValue1421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1421) = mixedMoment B node1421 node1421Labels := rfl
  simpa [nodeValue1421, Sparse.eval] using hc.symm

theorem sound1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1422 node1422Labels = Sparse.eval nodeValue1422 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1422) = mixedMoment B node1422 node1422Labels := rfl
  simpa [nodeValue1422, Sparse.eval] using hc.symm

theorem sound1423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1423 node1423Labels = Sparse.eval nodeValue1423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1423) = mixedMoment B node1423 node1423Labels := rfl
  simpa [nodeValue1423, Sparse.eval] using hc.symm

theorem sound1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1424 node1424Labels = Sparse.eval nodeValue1424 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1424) = mixedMoment B node1424 node1424Labels := rfl
  simpa [nodeValue1424, Sparse.eval] using hc.symm

theorem sound1425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1425 node1425Labels = Sparse.eval nodeValue1425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1425) = mixedMoment B node1425 node1425Labels := rfl
  simpa [nodeValue1425, Sparse.eval] using hc.symm

theorem sound1426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1426 node1426Labels = Sparse.eval nodeValue1426 (mixedVector B) := by
  have h := singleton1426 B _hB
  rw [sound84 B _hB _hF] at h
  norm_num [nodeValue1426, nodeValue84, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1427 node1427Labels = Sparse.eval nodeValue1427 (mixedVector B) := by
  have h := singleton1427 B _hB
  rw [sound83 B _hB _hF] at h
  norm_num [nodeValue1427, nodeValue83, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1428 node1428Labels = Sparse.eval nodeValue1428 (mixedVector B) := by
  simpa only [nodeValue1428, Sparse.eval_nil] using zero1428 B _hB _hF

theorem sound1429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1429 node1429Labels = Sparse.eval nodeValue1429 (mixedVector B) := by
  have h := singleton1429 B _hB
  rw [sound85 B _hB _hF] at h
  norm_num [nodeValue1429, nodeValue85, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1430 node1430Labels = Sparse.eval nodeValue1430 (mixedVector B) := by
  have h := singleton1430 B _hB
  rw [sound86 B _hB _hF] at h
  norm_num [nodeValue1430, nodeValue86, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1431 node1431Labels = Sparse.eval nodeValue1431 (mixedVector B) := by
  simpa only [nodeValue1431, Sparse.eval_nil] using zero1431 B _hB _hF

theorem sound1432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1432 node1432Labels = Sparse.eval nodeValue1432 (mixedVector B) := by
  simpa only [nodeValue1432, Sparse.eval_nil] using zero1432 B _hB _hF

theorem sound1433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1433 node1433Labels = Sparse.eval nodeValue1433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1433) = mixedMoment B node1433 node1433Labels := rfl
  simpa [nodeValue1433, Sparse.eval] using hc.symm

theorem sound1434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1434 node1434Labels = Sparse.eval nodeValue1434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1434) = mixedMoment B node1434 node1434Labels := rfl
  simpa [nodeValue1434, Sparse.eval] using hc.symm

theorem sound1435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1435 node1435Labels = Sparse.eval nodeValue1435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1435) = mixedMoment B node1435 node1435Labels := rfl
  simpa [nodeValue1435, Sparse.eval] using hc.symm

theorem sound1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1436 node1436Labels = Sparse.eval nodeValue1436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1436) = mixedMoment B node1436 node1436Labels := rfl
  simpa [nodeValue1436, Sparse.eval] using hc.symm

theorem sound1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1437 node1437Labels = Sparse.eval nodeValue1437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1437) = mixedMoment B node1437 node1437Labels := rfl
  simpa [nodeValue1437, Sparse.eval] using hc.symm

theorem sound1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1438 node1438Labels = Sparse.eval nodeValue1438 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1438) = mixedMoment B node1438 node1438Labels := rfl
  simpa [nodeValue1438, Sparse.eval] using hc.symm

theorem sound1439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1439 node1439Labels = Sparse.eval nodeValue1439 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1439) = mixedMoment B node1439 node1439Labels := rfl
  simpa [nodeValue1439, Sparse.eval] using hc.symm

theorem sound1440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1440 node1440Labels = Sparse.eval nodeValue1440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1440) = mixedMoment B node1440 node1440Labels := rfl
  simpa [nodeValue1440, Sparse.eval] using hc.symm

theorem sound1441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1441 node1441Labels = Sparse.eval nodeValue1441 (mixedVector B) := by
  have h := singleton1441 B _hB
  rw [sound108 B _hB _hF] at h
  norm_num [nodeValue1441, nodeValue108, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1442 node1442Labels = Sparse.eval nodeValue1442 (mixedVector B) := by
  have h := singleton1442 B _hB
  rw [sound111 B _hB _hF] at h
  norm_num [nodeValue1442, nodeValue111, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1443 node1443Labels = Sparse.eval nodeValue1443 (mixedVector B) := by
  have h := singleton1443 B _hB
  rw [sound110 B _hB _hF] at h
  norm_num [nodeValue1443, nodeValue110, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1444 node1444Labels = Sparse.eval nodeValue1444 (mixedVector B) := by
  have h := singleton1444 B _hB
  rw [sound106 B _hB _hF] at h
  norm_num [nodeValue1444, nodeValue106, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1445 node1445Labels = Sparse.eval nodeValue1445 (mixedVector B) := by
  have h := singleton1445 B _hB
  rw [sound112 B _hB _hF] at h
  norm_num [nodeValue1445, nodeValue112, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1446 node1446Labels = Sparse.eval nodeValue1446 (mixedVector B) := by
  simpa only [nodeValue1446, Sparse.eval_nil] using zero1446 B _hB _hF

theorem sound1447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1447 node1447Labels = Sparse.eval nodeValue1447 (mixedVector B) := by
  simpa only [nodeValue1447, Sparse.eval_nil] using zero1447 B _hB _hF

theorem sound1448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1448 node1448Labels = Sparse.eval nodeValue1448 (mixedVector B) := by
  simpa only [nodeValue1448, Sparse.eval_nil] using zero1448 B _hB _hF

theorem sound1449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1449 node1449Labels = Sparse.eval nodeValue1449 (mixedVector B) := by
  have h := singleton1449 B _hB
  rw [sound105 B _hB _hF] at h
  norm_num [nodeValue1449, nodeValue105, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1450 node1450Labels = Sparse.eval nodeValue1450 (mixedVector B) := by
  simpa only [nodeValue1450, Sparse.eval_nil] using zero1450 B _hB _hF

theorem sound1451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1451 node1451Labels = Sparse.eval nodeValue1451 (mixedVector B) := by
  have h := singleton1451 B _hB
  rw [sound109 B _hB _hF] at h
  norm_num [nodeValue1451, nodeValue109, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1452 node1452Labels = Sparse.eval nodeValue1452 (mixedVector B) := by
  simpa only [nodeValue1452, Sparse.eval_nil] using zero1452 B _hB _hF

theorem sound1453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1453 node1453Labels = Sparse.eval nodeValue1453 (mixedVector B) := by
  have h := singleton1453 B _hB
  rw [sound107 B _hB _hF] at h
  norm_num [nodeValue1453, nodeValue107, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1454 node1454Labels = Sparse.eval nodeValue1454 (mixedVector B) := by
  have h := singleton1454 B _hB
  rw [sound113 B _hB _hF] at h
  norm_num [nodeValue1454, nodeValue113, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1455 node1455Labels = Sparse.eval nodeValue1455 (mixedVector B) := by
  simpa only [nodeValue1455, Sparse.eval_nil] using zero1455 B _hB _hF

theorem sound1456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1456 node1456Labels = Sparse.eval nodeValue1456 (mixedVector B) := by
  simpa only [nodeValue1456, Sparse.eval_nil] using zero1456 B _hB _hF

theorem sound1457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1457 node1457Labels = Sparse.eval nodeValue1457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1457) = mixedMoment B node1457 node1457Labels := rfl
  simpa [nodeValue1457, Sparse.eval] using hc.symm

theorem sound1458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1458 node1458Labels = Sparse.eval nodeValue1458 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1458) = mixedMoment B node1458 node1458Labels := rfl
  simpa [nodeValue1458, Sparse.eval] using hc.symm

theorem sound1459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1459 node1459Labels = Sparse.eval nodeValue1459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1459) = mixedMoment B node1459 node1459Labels := rfl
  simpa [nodeValue1459, Sparse.eval] using hc.symm

theorem sound1460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1460 node1460Labels = Sparse.eval nodeValue1460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1460) = mixedMoment B node1460 node1460Labels := rfl
  simpa [nodeValue1460, Sparse.eval] using hc.symm

theorem sound1461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1461 node1461Labels = Sparse.eval nodeValue1461 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1461) = mixedMoment B node1461 node1461Labels := rfl
  simpa [nodeValue1461, Sparse.eval] using hc.symm

theorem sound1462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1462 node1462Labels = Sparse.eval nodeValue1462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1462) = mixedMoment B node1462 node1462Labels := rfl
  simpa [nodeValue1462, Sparse.eval] using hc.symm

theorem sound1463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1463 node1463Labels = Sparse.eval nodeValue1463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1463) = mixedMoment B node1463 node1463Labels := rfl
  simpa [nodeValue1463, Sparse.eval] using hc.symm

theorem sound1464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1464 node1464Labels = Sparse.eval nodeValue1464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1464) = mixedMoment B node1464 node1464Labels := rfl
  simpa [nodeValue1464, Sparse.eval] using hc.symm

theorem sound1465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1465 node1465Labels = Sparse.eval nodeValue1465 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1465) = mixedMoment B node1465 node1465Labels := rfl
  simpa [nodeValue1465, Sparse.eval] using hc.symm

theorem sound1466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1466 node1466Labels = Sparse.eval nodeValue1466 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1466) = mixedMoment B node1466 node1466Labels := rfl
  simpa [nodeValue1466, Sparse.eval] using hc.symm

theorem sound1467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1467 node1467Labels = Sparse.eval nodeValue1467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1467) = mixedMoment B node1467 node1467Labels := rfl
  simpa [nodeValue1467, Sparse.eval] using hc.symm

theorem sound1468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1468 node1468Labels = Sparse.eval nodeValue1468 (mixedVector B) := by
  have h := singleton1468 B _hB
  rw [sound51 B _hB _hF] at h
  norm_num [nodeValue1468, nodeValue51, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1469 node1469Labels = Sparse.eval nodeValue1469 (mixedVector B) := by
  have h := singleton1469 B _hB
  rw [sound54 B _hB _hF] at h
  norm_num [nodeValue1469, nodeValue54, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1470 node1470Labels = Sparse.eval nodeValue1470 (mixedVector B) := by
  have h := singleton1470 B _hB
  rw [sound47 B _hB _hF] at h
  norm_num [nodeValue1470, nodeValue47, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1471 node1471Labels = Sparse.eval nodeValue1471 (mixedVector B) := by
  have h := singleton1471 B _hB
  rw [sound53 B _hB _hF] at h
  norm_num [nodeValue1471, nodeValue53, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
