import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1440 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

theorem canonical1440 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1440 = injectiveMoment H node156 := by
  rfl

def raw1441 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical1441 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1441 = injectiveMoment H node157 := by
  rfl

def raw1442 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![2, -2, 0]]

theorem canonical1442 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1442 = injectiveMoment H node33 := by
  rfl

def raw1443 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 4, -5]]

theorem canonical1443 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1443 = injectiveMoment H node34 := by
  rfl

def raw1444 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -1, 0], ![0, 1, -1], ![1, 2, -3]]

def raw1444step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical1444 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1444 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw1444 = injectiveMoment H raw1444step0 := by
      have heq : raw1444step0 = (fun i j => raw1444 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1444 permutation11 permutation3
    _ = injectiveMoment H node149 := by rfl

def raw1445 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -1, 0], ![1, 1, -2], ![0, 2, -2]]

def raw1445step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1445 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1445 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw1445 = injectiveMoment H raw1445step0 := by
      have heq : raw1445step0 = (fun i j => raw1445 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1445 permutation13 permutation3
    _ = injectiveMoment H node153 := by rfl

def raw1446 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -1, 0], ![1, 3, -4]]

def raw1446step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![4, 0, -4]]

def raw1446step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical1446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1446 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1446 = injectiveMoment H raw1446step0 := by
      have heq : raw1446step0 = raw1446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1446).symm
    injectiveMoment H raw1446step0 = injectiveMoment H raw1446step1 := by
      have heq : raw1446step1 = (fun i j => raw1446step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1446step0 permutation6 permutation5
    _ = injectiveMoment H node59 := by rfl

def raw1447 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 0, -1], ![1, 2, -3]]

def raw1447step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![4, -1, -3]]

def raw1447step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical1447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1447 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1447 = injectiveMoment H raw1447step0 := by
      have heq : raw1447step0 = raw1447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1447).symm
    injectiveMoment H raw1447step0 = injectiveMoment H raw1447step1 := by
      have heq : raw1447step1 = (fun i j => raw1447step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1447step0 permutation8 permutation6
    _ = injectiveMoment H node52 := by rfl

def raw1448 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![0, 2, -2], ![1, -1, 0]]

def raw1448step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1448 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1448 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw1448 = injectiveMoment H raw1448step0 := by
      have heq : raw1448step0 = (fun i j => raw1448 (permutation12 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1448 permutation12 permutation3
    _ = injectiveMoment H node153 := by rfl

def raw1449 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

theorem canonical1449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1449 = injectiveMoment H node35 := by
  rfl

def raw1450 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 2, -3], ![1, 0, -1]]

def raw1450step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![4, -3, -1]]

def raw1450step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical1450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1450 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1450 = injectiveMoment H raw1450step0 := by
      have heq : raw1450step0 = raw1450.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1450).symm
    injectiveMoment H raw1450step0 = injectiveMoment H raw1450step1 := by
      have heq : raw1450step1 = (fun i j => raw1450step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1450step0 permutation8 permutation8
    _ = injectiveMoment H node52 := by rfl

def raw1451 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 3, -4], ![1, -1, 0]]

def raw1451step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![4, -4, 0]]

def raw1451step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical1451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1451 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1451 = injectiveMoment H raw1451step0 := by
      have heq : raw1451step0 = raw1451.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1451).symm
    injectiveMoment H raw1451step0 = injectiveMoment H raw1451step1 := by
      have heq : raw1451step1 = (fun i j => raw1451step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1451step0 permutation6 permutation7
    _ = injectiveMoment H node59 := by rfl

def raw1452 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 4, -5], ![1, -2, 1]]

def raw1452step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 4, -5]]

theorem canonical1452 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1452 = injectiveMoment H node34 := by
  calc
    injectiveMoment H raw1452 = injectiveMoment H raw1452step0 := by
      have heq : raw1452step0 = (fun i j => raw1452 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1452 permutation4 permutation3
    _ = injectiveMoment H node34 := by rfl

def raw1453 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, -2, 5, -1], ![2, 2, -5, 1]]

def raw1453step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![5, -5], ![-1, 1]]

def raw1453step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical1453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1453 = injectiveMoment H node13 := by
  calc
    injectiveMoment H raw1453 = injectiveMoment H raw1453step0 := by
      have heq : raw1453step0 = raw1453.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1453).symm
    injectiveMoment H raw1453step0 = injectiveMoment H raw1453step1 := by
      have heq : raw1453step1 = (fun i j => raw1453step0 (permutation25 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1453step0 permutation25 permutation2
    _ = injectiveMoment H node13 := by rfl

def raw1454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical1454 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1454 = injectiveMoment H node2386 := by
  calc
    injectiveMoment H raw1454 = injectiveMoment H raw1454step0 := by
      have heq : raw1454step0 = (fun i j => raw1454 (permutation49 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1454 permutation49 permutation17
    _ = injectiveMoment H node2386 := by rfl

def raw1455 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1455step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical1455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1455 = injectiveMoment H node754 := by
  calc
    injectiveMoment H raw1455 = injectiveMoment H raw1455step0 := by
      have heq : raw1455step0 = (fun i j => raw1455 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1455 permutation10 permutation15
    _ = injectiveMoment H node754 := by rfl

def raw1456 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1456step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1456 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1456 = injectiveMoment H node751 := by
  calc
    injectiveMoment H raw1456 = injectiveMoment H raw1456step0 := by
      have heq : raw1456step0 = (fun i j => raw1456 (permutation11 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1456 permutation11 permutation17
    _ = injectiveMoment H node751 := by rfl

def raw1457 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1457step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-2, 0, 0, 2], ![5, -1, -1, -3]]

def raw1457step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1457 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1457 = injectiveMoment H node890 := by
  calc
    injectiveMoment H raw1457 = injectiveMoment H raw1457step0 := by
      have heq : raw1457step0 = raw1457.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1457).symm
    injectiveMoment H raw1457step0 = injectiveMoment H raw1457step1 := by
      have heq : raw1457step1 = (fun i j => raw1457step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1457step0 permutation32 permutation24
    _ = injectiveMoment H node890 := by rfl

def raw1458 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw1458step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1458 = injectiveMoment H node755 := by
  calc
    injectiveMoment H raw1458 = injectiveMoment H raw1458step0 := by
      have heq : raw1458step0 = (fun i j => raw1458 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1458 permutation12 permutation15
    _ = injectiveMoment H node755 := by rfl

def raw1459 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1459step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1459 = injectiveMoment H node750 := by
  calc
    injectiveMoment H raw1459 = injectiveMoment H raw1459step0 := by
      have heq : raw1459step0 = (fun i j => raw1459 (permutation12 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1459 permutation12 permutation17
    _ = injectiveMoment H node750 := by rfl

def raw1460 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1460step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-2, 2, 0, 0], ![5, -3, -1, -1]]

def raw1460step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical1460 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1460 = injectiveMoment H node888 := by
  calc
    injectiveMoment H raw1460 = injectiveMoment H raw1460step0 := by
      have heq : raw1460step0 = raw1460.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1460).symm
    injectiveMoment H raw1460step0 = injectiveMoment H raw1460step1 := by
      have heq : raw1460step1 = (fun i j => raw1460step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1460step0 permutation30 permutation26
    _ = injectiveMoment H node888 := by rfl

def raw1461 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem canonical1461 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1461 = injectiveMoment H node1548 := by
  rfl

def raw1462 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical1462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1462 = injectiveMoment H node1549 := by
  rfl

def raw1463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical1463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1463 = injectiveMoment H node1550 := by
  rfl

def raw1464 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

theorem canonical1464 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1464 = injectiveMoment H node1551 := by
  rfl

def raw1465 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

theorem canonical1465 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1465 = injectiveMoment H node1552 := by
  rfl

def raw1466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical1466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1466 = injectiveMoment H node1553 := by
  rfl

def raw1467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical1467 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1467 = injectiveMoment H node1554 := by
  rfl

def raw1468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical1468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1468 = injectiveMoment H node1555 := by
  rfl

def raw1469 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem canonical1469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1469 = injectiveMoment H node1556 := by
  rfl

def raw1470 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1470 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1470 = injectiveMoment H node1557 := by
  rfl

def raw1471 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical1471 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1471 = injectiveMoment H node1559 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
