import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons23

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1472 node1472Labels = Sparse.eval nodeValue1472 (mixedVector B) := by
  have h := singleton1472 B _hB
  rw [sound55 B _hB _hF] at h
  norm_num [nodeValue1472, nodeValue55, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1473 node1473Labels = Sparse.eval nodeValue1473 (mixedVector B) := by
  have h := singleton1473 B _hB
  rw [sound56 B _hB _hF] at h
  norm_num [nodeValue1473, nodeValue56, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1474 node1474Labels = Sparse.eval nodeValue1474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1474) = mixedMoment B node1474 node1474Labels := rfl
  simpa [nodeValue1474, Sparse.eval] using hc.symm

theorem sound1475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1475 node1475Labels = Sparse.eval nodeValue1475 (mixedVector B) := by
  have h := singleton1475 B _hB
  rw [sound44 B _hB _hF] at h
  norm_num [nodeValue1475, nodeValue44, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1476 node1476Labels = Sparse.eval nodeValue1476 (mixedVector B) := by
  have h := singleton1476 B _hB
  rw [sound46 B _hB _hF] at h
  norm_num [nodeValue1476, nodeValue46, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1477 node1477Labels = Sparse.eval nodeValue1477 (mixedVector B) := by
  have h := singleton1477 B _hB
  rw [sound43 B _hB _hF] at h
  norm_num [nodeValue1477, nodeValue43, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1478 node1478Labels = Sparse.eval nodeValue1478 (mixedVector B) := by
  have h := singleton1478 B _hB
  rw [sound45 B _hB _hF] at h
  norm_num [nodeValue1478, nodeValue45, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1479 node1479Labels = Sparse.eval nodeValue1479 (mixedVector B) := by
  have h := singleton1479 B _hB
  rw [sound48 B _hB _hF] at h
  norm_num [nodeValue1479, nodeValue48, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1480 node1480Labels = Sparse.eval nodeValue1480 (mixedVector B) := by
  have h := singleton1480 B _hB
  rw [sound50 B _hB _hF] at h
  norm_num [nodeValue1480, nodeValue50, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1481 node1481Labels = Sparse.eval nodeValue1481 (mixedVector B) := by
  have h := singleton1481 B _hB
  rw [sound52 B _hB _hF] at h
  norm_num [nodeValue1481, nodeValue52, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1482 node1482Labels = Sparse.eval nodeValue1482 (mixedVector B) := by
  simpa only [nodeValue1482, Sparse.eval_nil] using zero1482 B _hB _hF

theorem sound1483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1483 node1483Labels = Sparse.eval nodeValue1483 (mixedVector B) := by
  simpa only [nodeValue1483, Sparse.eval_nil] using zero1483 B _hB _hF

theorem sound1484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1484 node1484Labels = Sparse.eval nodeValue1484 (mixedVector B) := by
  simpa only [nodeValue1484, Sparse.eval_nil] using zero1484 B _hB _hF

theorem sound1485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1485 node1485Labels = Sparse.eval nodeValue1485 (mixedVector B) := by
  simpa only [nodeValue1485, Sparse.eval_nil] using zero1485 B _hB _hF

theorem sound1486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1486 node1486Labels = Sparse.eval nodeValue1486 (mixedVector B) := by
  simpa only [nodeValue1486, Sparse.eval_nil] using zero1486 B _hB _hF

theorem sound1487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1487 node1487Labels = Sparse.eval nodeValue1487 (mixedVector B) := by
  simpa only [nodeValue1487, Sparse.eval_nil] using zero1487 B _hB _hF

theorem sound1488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1488 node1488Labels = Sparse.eval nodeValue1488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1488) = mixedMoment B node1488 node1488Labels := rfl
  simpa [nodeValue1488, Sparse.eval] using hc.symm

theorem sound1489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1489 node1489Labels = Sparse.eval nodeValue1489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1489) = mixedMoment B node1489 node1489Labels := rfl
  simpa [nodeValue1489, Sparse.eval] using hc.symm

theorem sound1490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1490 node1490Labels = Sparse.eval nodeValue1490 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1490) = mixedMoment B node1490 node1490Labels := rfl
  simpa [nodeValue1490, Sparse.eval] using hc.symm

theorem sound1491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1491 node1491Labels = Sparse.eval nodeValue1491 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1491) = mixedMoment B node1491 node1491Labels := rfl
  simpa [nodeValue1491, Sparse.eval] using hc.symm

theorem sound1492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1492 node1492Labels = Sparse.eval nodeValue1492 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1492) = mixedMoment B node1492 node1492Labels := rfl
  simpa [nodeValue1492, Sparse.eval] using hc.symm

theorem sound1493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1493 node1493Labels = Sparse.eval nodeValue1493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1493) = mixedMoment B node1493 node1493Labels := rfl
  simpa [nodeValue1493, Sparse.eval] using hc.symm

theorem sound1494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1494 node1494Labels = Sparse.eval nodeValue1494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1494) = mixedMoment B node1494 node1494Labels := rfl
  simpa [nodeValue1494, Sparse.eval] using hc.symm

theorem sound1495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1495 node1495Labels = Sparse.eval nodeValue1495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1495) = mixedMoment B node1495 node1495Labels := rfl
  simpa [nodeValue1495, Sparse.eval] using hc.symm

theorem sound1496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1496 node1496Labels = Sparse.eval nodeValue1496 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1496) = mixedMoment B node1496 node1496Labels := rfl
  simpa [nodeValue1496, Sparse.eval] using hc.symm

theorem sound1497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1497 node1497Labels = Sparse.eval nodeValue1497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1497) = mixedMoment B node1497 node1497Labels := rfl
  simpa [nodeValue1497, Sparse.eval] using hc.symm

theorem sound1498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1498 node1498Labels = Sparse.eval nodeValue1498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1498) = mixedMoment B node1498 node1498Labels := rfl
  simpa [nodeValue1498, Sparse.eval] using hc.symm

theorem sound1499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1499 node1499Labels = Sparse.eval nodeValue1499 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1499) = mixedMoment B node1499 node1499Labels := rfl
  simpa [nodeValue1499, Sparse.eval] using hc.symm

theorem sound1500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1500 node1500Labels = Sparse.eval nodeValue1500 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1500) = mixedMoment B node1500 node1500Labels := rfl
  simpa [nodeValue1500, Sparse.eval] using hc.symm

theorem sound1501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1501 node1501Labels = Sparse.eval nodeValue1501 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1501) = mixedMoment B node1501 node1501Labels := rfl
  simpa [nodeValue1501, Sparse.eval] using hc.symm

theorem sound1502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1502 node1502Labels = Sparse.eval nodeValue1502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1502) = mixedMoment B node1502 node1502Labels := rfl
  simpa [nodeValue1502, Sparse.eval] using hc.symm

theorem sound1503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1503 node1503Labels = Sparse.eval nodeValue1503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1503) = mixedMoment B node1503 node1503Labels := rfl
  simpa [nodeValue1503, Sparse.eval] using hc.symm

theorem sound1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1504 node1504Labels = Sparse.eval nodeValue1504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1504) = mixedMoment B node1504 node1504Labels := rfl
  simpa [nodeValue1504, Sparse.eval] using hc.symm

theorem sound1505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1505 node1505Labels = Sparse.eval nodeValue1505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1505) = mixedMoment B node1505 node1505Labels := rfl
  simpa [nodeValue1505, Sparse.eval] using hc.symm

theorem sound1506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1506 node1506Labels = Sparse.eval nodeValue1506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1506) = mixedMoment B node1506 node1506Labels := rfl
  simpa [nodeValue1506, Sparse.eval] using hc.symm

theorem sound1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1507 node1507Labels = Sparse.eval nodeValue1507 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1507) = mixedMoment B node1507 node1507Labels := rfl
  simpa [nodeValue1507, Sparse.eval] using hc.symm

theorem sound1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1508 node1508Labels = Sparse.eval nodeValue1508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1508) = mixedMoment B node1508 node1508Labels := rfl
  simpa [nodeValue1508, Sparse.eval] using hc.symm

theorem sound1509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1509 node1509Labels = Sparse.eval nodeValue1509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1509) = mixedMoment B node1509 node1509Labels := rfl
  simpa [nodeValue1509, Sparse.eval] using hc.symm

theorem sound1510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1510 node1510Labels = Sparse.eval nodeValue1510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1510) = mixedMoment B node1510 node1510Labels := rfl
  simpa [nodeValue1510, Sparse.eval] using hc.symm

theorem sound1511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1511 node1511Labels = Sparse.eval nodeValue1511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1511) = mixedMoment B node1511 node1511Labels := rfl
  simpa [nodeValue1511, Sparse.eval] using hc.symm

theorem sound1512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1512 node1512Labels = Sparse.eval nodeValue1512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1512) = mixedMoment B node1512 node1512Labels := rfl
  simpa [nodeValue1512, Sparse.eval] using hc.symm

theorem sound1513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1513 node1513Labels = Sparse.eval nodeValue1513 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1513) = mixedMoment B node1513 node1513Labels := rfl
  simpa [nodeValue1513, Sparse.eval] using hc.symm

theorem sound1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1514 node1514Labels = Sparse.eval nodeValue1514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1514) = mixedMoment B node1514 node1514Labels := rfl
  simpa [nodeValue1514, Sparse.eval] using hc.symm

theorem sound1515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1515 node1515Labels = Sparse.eval nodeValue1515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1515) = mixedMoment B node1515 node1515Labels := rfl
  simpa [nodeValue1515, Sparse.eval] using hc.symm

theorem sound1516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1516 node1516Labels = Sparse.eval nodeValue1516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1516) = mixedMoment B node1516 node1516Labels := rfl
  simpa [nodeValue1516, Sparse.eval] using hc.symm

theorem sound1517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1517 node1517Labels = Sparse.eval nodeValue1517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1517) = mixedMoment B node1517 node1517Labels := rfl
  simpa [nodeValue1517, Sparse.eval] using hc.symm

theorem sound1518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1518 node1518Labels = Sparse.eval nodeValue1518 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1518) = mixedMoment B node1518 node1518Labels := rfl
  simpa [nodeValue1518, Sparse.eval] using hc.symm

theorem sound1519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1519 node1519Labels = Sparse.eval nodeValue1519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1519) = mixedMoment B node1519 node1519Labels := rfl
  simpa [nodeValue1519, Sparse.eval] using hc.symm

theorem sound1520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1520 node1520Labels = Sparse.eval nodeValue1520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1520) = mixedMoment B node1520 node1520Labels := rfl
  simpa [nodeValue1520, Sparse.eval] using hc.symm

theorem sound1521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1521 node1521Labels = Sparse.eval nodeValue1521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1521) = mixedMoment B node1521 node1521Labels := rfl
  simpa [nodeValue1521, Sparse.eval] using hc.symm

theorem sound1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1522 node1522Labels = Sparse.eval nodeValue1522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1522) = mixedMoment B node1522 node1522Labels := rfl
  simpa [nodeValue1522, Sparse.eval] using hc.symm

theorem sound1523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1523 node1523Labels = Sparse.eval nodeValue1523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1523) = mixedMoment B node1523 node1523Labels := rfl
  simpa [nodeValue1523, Sparse.eval] using hc.symm

theorem sound1524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1524 node1524Labels = Sparse.eval nodeValue1524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1524) = mixedMoment B node1524 node1524Labels := rfl
  simpa [nodeValue1524, Sparse.eval] using hc.symm

theorem sound1525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1525 node1525Labels = Sparse.eval nodeValue1525 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1525) = mixedMoment B node1525 node1525Labels := rfl
  simpa [nodeValue1525, Sparse.eval] using hc.symm

theorem sound1526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1526 node1526Labels = Sparse.eval nodeValue1526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1526) = mixedMoment B node1526 node1526Labels := rfl
  simpa [nodeValue1526, Sparse.eval] using hc.symm

theorem sound1527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1527 node1527Labels = Sparse.eval nodeValue1527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1527) = mixedMoment B node1527 node1527Labels := rfl
  simpa [nodeValue1527, Sparse.eval] using hc.symm

theorem sound1528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1528 node1528Labels = Sparse.eval nodeValue1528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1528) = mixedMoment B node1528 node1528Labels := rfl
  simpa [nodeValue1528, Sparse.eval] using hc.symm

theorem sound1529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1529 node1529Labels = Sparse.eval nodeValue1529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1529) = mixedMoment B node1529 node1529Labels := rfl
  simpa [nodeValue1529, Sparse.eval] using hc.symm

theorem sound1530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1530 node1530Labels = Sparse.eval nodeValue1530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1530) = mixedMoment B node1530 node1530Labels := rfl
  simpa [nodeValue1530, Sparse.eval] using hc.symm

theorem sound1531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1531 node1531Labels = Sparse.eval nodeValue1531 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1531) = mixedMoment B node1531 node1531Labels := rfl
  simpa [nodeValue1531, Sparse.eval] using hc.symm

theorem sound1532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1532 node1532Labels = Sparse.eval nodeValue1532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1532) = mixedMoment B node1532 node1532Labels := rfl
  simpa [nodeValue1532, Sparse.eval] using hc.symm

theorem sound1533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1533 node1533Labels = Sparse.eval nodeValue1533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1533) = mixedMoment B node1533 node1533Labels := rfl
  simpa [nodeValue1533, Sparse.eval] using hc.symm

theorem sound1534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1534 node1534Labels = Sparse.eval nodeValue1534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1534) = mixedMoment B node1534 node1534Labels := rfl
  simpa [nodeValue1534, Sparse.eval] using hc.symm

theorem sound1535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1535 node1535Labels = Sparse.eval nodeValue1535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1535) = mixedMoment B node1535 node1535Labels := rfl
  simpa [nodeValue1535, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
