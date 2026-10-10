import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1472 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1472 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1472 = injectiveMoment H node1561 := by
  rfl

def raw1473 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical1473 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1473 = injectiveMoment H node1562 := by
  rfl

def raw1474 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical1474 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1474 = injectiveMoment H node1563 := by
  rfl

def raw1475 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem canonical1475 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1475 = injectiveMoment H node1564 := by
  rfl

def raw1476 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical1476 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1476 = injectiveMoment H node1565 := by
  rfl

def raw1477 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical1477 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1477 = injectiveMoment H node1566 := by
  rfl

def raw1478 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical1478 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1478 = injectiveMoment H node1567 := by
  rfl

def raw1479 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical1479 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1479 = injectiveMoment H node1568 := by
  rfl

def raw1480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem canonical1480 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1480 = injectiveMoment H node1569 := by
  rfl

def raw1481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem canonical1481 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1481 = injectiveMoment H node1570 := by
  rfl

def raw1482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1482 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1482 = injectiveMoment H node1571 := by
  rfl

def raw1483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1483step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical1483 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1483 = injectiveMoment H node1549 := by
  calc
    injectiveMoment H raw1483 = injectiveMoment H raw1483step0 := by
      have heq : raw1483step0 = (fun i j => raw1483 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1483 permutation41 permutation11
    _ = injectiveMoment H node1549 := by rfl

def raw1484 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1484 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1484 = injectiveMoment H node1572 := by
  rfl

def raw1485 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1485step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1485 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1485 = injectiveMoment H node1561 := by
  calc
    injectiveMoment H raw1485 = injectiveMoment H raw1485step0 := by
      have heq : raw1485step0 = (fun i j => raw1485 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1485 permutation39 permutation11
    _ = injectiveMoment H node1561 := by rfl

def raw1486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![-1, 2, -1, 0], ![4, -1, 0, -3]]

def raw1486step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, 1, -1, -1], ![1, -2, 1, 0], ![-4, 1, 0, 3]]

def raw1486step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical1486 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1486 = injectiveMoment H node1348 := by
  calc
    injectiveMoment H raw1486 = injectiveMoment H raw1486step0 := by
      have heq : raw1486step0 = raw1486.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1486).symm
    injectiveMoment H raw1486step0 = injectiveMoment H raw1486step1 := by
      have heq : raw1486step1 = -raw1486step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1486step0).symm
    injectiveMoment H raw1486step1 = injectiveMoment H raw1486step2 := by
      have heq : raw1486step2 = (fun i j => raw1486step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1486step1 permutation16 permutation24
    _ = injectiveMoment H node1348 := by rfl

def raw1487 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1487 = injectiveMoment H node1573 := by
  rfl

def raw1488 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical1488 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1488 = injectiveMoment H node1574 := by
  rfl

def raw1489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical1489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1489 = injectiveMoment H node1575 := by
  rfl

def raw1490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1490 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1490 = injectiveMoment H node1576 := by
  rfl

def raw1491 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical1491 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1491 = injectiveMoment H node1577 := by
  rfl

def raw1492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1492step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1492 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1492 = injectiveMoment H node1576 := by
  calc
    injectiveMoment H raw1492 = injectiveMoment H raw1492step0 := by
      have heq : raw1492step0 = (fun i j => raw1492 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1492 permutation34 permutation9
    _ = injectiveMoment H node1576 := by rfl

def raw1493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1493step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![-1, 2, 0, -1], ![4, -1, -1, -2]]

def raw1493step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical1493 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1493 = injectiveMoment H node917 := by
  calc
    injectiveMoment H raw1493 = injectiveMoment H raw1493step0 := by
      have heq : raw1493step0 = raw1493.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1493).symm
    injectiveMoment H raw1493step0 = injectiveMoment H raw1493step1 := by
      have heq : raw1493step1 = (fun i j => raw1493step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1493step0 permutation28 permutation24
    _ = injectiveMoment H node917 := by rfl

def raw1494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

theorem canonical1494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1494 = injectiveMoment H node447 := by
  rfl

def raw1495 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1495 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1495 = injectiveMoment H node1578 := by
  rfl

def raw1496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

theorem canonical1496 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1496 = injectiveMoment H node448 := by
  rfl

def raw1497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical1497 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1497 = injectiveMoment H node1579 := by
  rfl

def raw1498 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1498 = injectiveMoment H node1580 := by
  rfl

def raw1499 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical1499 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1499 = injectiveMoment H node449 := by
  rfl

def raw1500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical1500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1500 = injectiveMoment H node1581 := by
  rfl

def raw1501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical1501 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1501 = injectiveMoment H node450 := by
  rfl

def raw1502 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, 0, -2, 0]]

theorem canonical1502 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1502 = injectiveMoment H node451 := by
  rfl

def raw1503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![-1, 2, -1, 0], ![4, -1, 0, -3]]

def raw1503step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, 0, -2], ![1, -2, 1, 0], ![-4, 1, 0, 3]]

def raw1503step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical1503 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1503 = injectiveMoment H node1278 := by
  calc
    injectiveMoment H raw1503 = injectiveMoment H raw1503step0 := by
      have heq : raw1503step0 = raw1503.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1503).symm
    injectiveMoment H raw1503step0 = injectiveMoment H raw1503step1 := by
      have heq : raw1503step1 = -raw1503step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1503step0).symm
    injectiveMoment H raw1503step1 = injectiveMoment H raw1503step2 := by
      have heq : raw1503step2 = (fun i j => raw1503step1 (permutation10 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1503step1 permutation10 permutation24
    _ = injectiveMoment H node1278 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
