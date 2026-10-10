import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound46
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1472 : keyMomentRows (1472 : Fin 2886) =
    keyMomentRow1472 := by decide +kernel

theorem keyMomentRowsAt1473 : keyMomentRows (1473 : Fin 2886) =
    keyMomentRow1473 := by decide +kernel

theorem keyMomentRowsAt1474 : keyMomentRows (1474 : Fin 2886) =
    keyMomentRow1474 := by decide +kernel

theorem keyMomentRowsAt1475 : keyMomentRows (1475 : Fin 2886) =
    keyMomentRow1475 := by decide +kernel

theorem keyMomentRowsAt1476 : keyMomentRows (1476 : Fin 2886) =
    keyMomentRow1476 := by decide +kernel

theorem keyMomentRowsAt1477 : keyMomentRows (1477 : Fin 2886) =
    keyMomentRow1477 := by decide +kernel

theorem keyMomentRowsAt1478 : keyMomentRows (1478 : Fin 2886) =
    keyMomentRow1478 := by decide +kernel

theorem keyMomentRowsAt1479 : keyMomentRows (1479 : Fin 2886) =
    keyMomentRow1479 := by decide +kernel

theorem keyMomentRowsAt1480 : keyMomentRows (1480 : Fin 2886) =
    keyMomentRow1480 := by decide +kernel

theorem keyMomentRowsAt1481 : keyMomentRows (1481 : Fin 2886) =
    keyMomentRow1481 := by decide +kernel

theorem keyMomentRowsAt1482 : keyMomentRows (1482 : Fin 2886) =
    keyMomentRow1482 := by decide +kernel

theorem keyMomentRowsAt1483 : keyMomentRows (1483 : Fin 2886) =
    keyMomentRow1483 := by decide +kernel

theorem keyMomentRowsAt1484 : keyMomentRows (1484 : Fin 2886) =
    keyMomentRow1484 := by decide +kernel

theorem keyMomentRowsAt1485 : keyMomentRows (1485 : Fin 2886) =
    keyMomentRow1485 := by decide +kernel

theorem keyMomentRowsAt1486 : keyMomentRows (1486 : Fin 2886) =
    keyMomentRow1486 := by decide +kernel

theorem keyMomentRowsAt1487 : keyMomentRows (1487 : Fin 2886) =
    keyMomentRow1487 := by decide +kernel

theorem keyMomentRowsAt1488 : keyMomentRows (1488 : Fin 2886) =
    keyMomentRow1488 := by decide +kernel

theorem keyMomentRowsAt1489 : keyMomentRows (1489 : Fin 2886) =
    keyMomentRow1489 := by decide +kernel

theorem keyMomentRowsAt1490 : keyMomentRows (1490 : Fin 2886) =
    keyMomentRow1490 := by decide +kernel

theorem keyMomentRowsAt1491 : keyMomentRows (1491 : Fin 2886) =
    keyMomentRow1491 := by decide +kernel

theorem keyMomentRowsAt1492 : keyMomentRows (1492 : Fin 2886) =
    keyMomentRow1492 := by decide +kernel

theorem keyMomentRowsAt1493 : keyMomentRows (1493 : Fin 2886) =
    keyMomentRow1493 := by decide +kernel

theorem keyMomentRowsAt1494 : keyMomentRows (1494 : Fin 2886) =
    keyMomentRow1494 := by decide +kernel

theorem keyMomentRowsAt1495 : keyMomentRows (1495 : Fin 2886) =
    keyMomentRow1495 := by decide +kernel

theorem keyMomentRowsAt1496 : keyMomentRows (1496 : Fin 2886) =
    keyMomentRow1496 := by decide +kernel

theorem keyMomentRowsAt1497 : keyMomentRows (1497 : Fin 2886) =
    keyMomentRow1497 := by decide +kernel

theorem keyMomentRowsAt1498 : keyMomentRows (1498 : Fin 2886) =
    keyMomentRow1498 := by decide +kernel

theorem keyMomentRowsAt1499 : keyMomentRows (1499 : Fin 2886) =
    keyMomentRow1499 := by decide +kernel

theorem keyMomentRowsAt1500 : keyMomentRows (1500 : Fin 2886) =
    keyMomentRow1500 := by decide +kernel

theorem keyMomentRowsAt1501 : keyMomentRows (1501 : Fin 2886) =
    keyMomentRow1501 := by decide +kernel

theorem keyMomentRowsAt1502 : keyMomentRows (1502 : Fin 2886) =
    keyMomentRow1502 := by decide +kernel

theorem keyMomentRowsAt1503 : keyMomentRows (1503 : Fin 2886) =
    keyMomentRow1503 := by decide +kernel

theorem keyMomentChunkSound46 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 46) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1472 ∨ k.val = 1473 ∨ k.val = 1474 ∨ k.val = 1475 ∨ k.val = 1476 ∨ k.val = 1477 ∨ k.val = 1478 ∨ k.val = 1479 ∨ k.val = 1480 ∨ k.val = 1481 ∨ k.val = 1482 ∨ k.val = 1483 ∨ k.val = 1484 ∨ k.val = 1485 ∨ k.val = 1486 ∨ k.val = 1487 ∨ k.val = 1488 ∨ k.val = 1489 ∨ k.val = 1490 ∨ k.val = 1491 ∨ k.val = 1492 ∨ k.val = 1493 ∨ k.val = 1494 ∨ k.val = 1495 ∨ k.val = 1496 ∨ k.val = 1497 ∨ k.val = 1498 ∨ k.val = 1499 ∨ k.val = 1500 ∨ k.val = 1501 ∨ k.val = 1502 ∨ k.val = 1503 := by omega
  rcases heq with h1472 | h1473 | h1474 | h1475 | h1476 | h1477 | h1478 | h1479 | h1480 | h1481 | h1482 | h1483 | h1484 | h1485 | h1486 | h1487 | h1488 | h1489 | h1490 | h1491 | h1492 | h1493 | h1494 | h1495 | h1496 | h1497 | h1498 | h1499 | h1500 | h1501 | h1502 | h1503
  · have he : k = (1472 : Fin 2886) := Fin.ext h1472
    subst k
    rw [keyMomentRowsAt1472]
    exact keyMoment1472 B hB
  · have he : k = (1473 : Fin 2886) := Fin.ext h1473
    subst k
    rw [keyMomentRowsAt1473]
    exact keyMoment1473 B hB
  · have he : k = (1474 : Fin 2886) := Fin.ext h1474
    subst k
    rw [keyMomentRowsAt1474]
    exact keyMoment1474 B hB
  · have he : k = (1475 : Fin 2886) := Fin.ext h1475
    subst k
    rw [keyMomentRowsAt1475]
    exact keyMoment1475 B hB
  · have he : k = (1476 : Fin 2886) := Fin.ext h1476
    subst k
    rw [keyMomentRowsAt1476]
    exact keyMoment1476 B hB
  · have he : k = (1477 : Fin 2886) := Fin.ext h1477
    subst k
    rw [keyMomentRowsAt1477]
    exact keyMoment1477 B hB
  · have he : k = (1478 : Fin 2886) := Fin.ext h1478
    subst k
    rw [keyMomentRowsAt1478]
    exact keyMoment1478 B hB
  · have he : k = (1479 : Fin 2886) := Fin.ext h1479
    subst k
    rw [keyMomentRowsAt1479]
    exact keyMoment1479 B hB
  · have he : k = (1480 : Fin 2886) := Fin.ext h1480
    subst k
    rw [keyMomentRowsAt1480]
    exact keyMoment1480 B hB
  · have he : k = (1481 : Fin 2886) := Fin.ext h1481
    subst k
    rw [keyMomentRowsAt1481]
    exact keyMoment1481 B hB
  · have he : k = (1482 : Fin 2886) := Fin.ext h1482
    subst k
    rw [keyMomentRowsAt1482]
    exact keyMoment1482 B hB
  · have he : k = (1483 : Fin 2886) := Fin.ext h1483
    subst k
    rw [keyMomentRowsAt1483]
    exact keyMoment1483 B hB
  · have he : k = (1484 : Fin 2886) := Fin.ext h1484
    subst k
    rw [keyMomentRowsAt1484]
    exact keyMoment1484 B hB
  · have he : k = (1485 : Fin 2886) := Fin.ext h1485
    subst k
    rw [keyMomentRowsAt1485]
    exact keyMoment1485 B hB
  · have he : k = (1486 : Fin 2886) := Fin.ext h1486
    subst k
    rw [keyMomentRowsAt1486]
    exact keyMoment1486 B hB
  · have he : k = (1487 : Fin 2886) := Fin.ext h1487
    subst k
    rw [keyMomentRowsAt1487]
    exact keyMoment1487 B hB
  · have he : k = (1488 : Fin 2886) := Fin.ext h1488
    subst k
    rw [keyMomentRowsAt1488]
    exact keyMoment1488 B hB
  · have he : k = (1489 : Fin 2886) := Fin.ext h1489
    subst k
    rw [keyMomentRowsAt1489]
    exact keyMoment1489 B hB
  · have he : k = (1490 : Fin 2886) := Fin.ext h1490
    subst k
    rw [keyMomentRowsAt1490]
    exact keyMoment1490 B hB
  · have he : k = (1491 : Fin 2886) := Fin.ext h1491
    subst k
    rw [keyMomentRowsAt1491]
    exact keyMoment1491 B hB
  · have he : k = (1492 : Fin 2886) := Fin.ext h1492
    subst k
    rw [keyMomentRowsAt1492]
    exact keyMoment1492 B hB
  · have he : k = (1493 : Fin 2886) := Fin.ext h1493
    subst k
    rw [keyMomentRowsAt1493]
    exact keyMoment1493 B hB
  · have he : k = (1494 : Fin 2886) := Fin.ext h1494
    subst k
    rw [keyMomentRowsAt1494]
    exact keyMoment1494 B hB
  · have he : k = (1495 : Fin 2886) := Fin.ext h1495
    subst k
    rw [keyMomentRowsAt1495]
    exact keyMoment1495 B hB
  · have he : k = (1496 : Fin 2886) := Fin.ext h1496
    subst k
    rw [keyMomentRowsAt1496]
    exact keyMoment1496 B hB
  · have he : k = (1497 : Fin 2886) := Fin.ext h1497
    subst k
    rw [keyMomentRowsAt1497]
    exact keyMoment1497 B hB
  · have he : k = (1498 : Fin 2886) := Fin.ext h1498
    subst k
    rw [keyMomentRowsAt1498]
    exact keyMoment1498 B hB
  · have he : k = (1499 : Fin 2886) := Fin.ext h1499
    subst k
    rw [keyMomentRowsAt1499]
    exact keyMoment1499 B hB
  · have he : k = (1500 : Fin 2886) := Fin.ext h1500
    subst k
    rw [keyMomentRowsAt1500]
    exact keyMoment1500 B hB
  · have he : k = (1501 : Fin 2886) := Fin.ext h1501
    subst k
    rw [keyMomentRowsAt1501]
    exact keyMoment1501 B hB
  · have he : k = (1502 : Fin 2886) := Fin.ext h1502
    subst k
    rw [keyMomentRowsAt1502]
    exact keyMoment1502 B hB
  · have he : k = (1503 : Fin 2886) := Fin.ext h1503
    subst k
    rw [keyMomentRowsAt1503]
    exact keyMoment1503 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
