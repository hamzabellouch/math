import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1536 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1536step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical1536 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1536 = injectiveMoment H node1568 := by
  calc
    injectiveMoment H raw1536 = injectiveMoment H raw1536step0 := by
      have heq : raw1536step0 = (fun i j => raw1536 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1536 permutation39 permutation9
    _ = injectiveMoment H node1568 := by rfl

def raw1537 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1537step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem canonical1537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1537 = injectiveMoment H node1569 := by
  calc
    injectiveMoment H raw1537 = injectiveMoment H raw1537step0 := by
      have heq : raw1537step0 = (fun i j => raw1537 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1537 permutation39 permutation9
    _ = injectiveMoment H node1569 := by rfl

def raw1538 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1538step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem canonical1538 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1538 = injectiveMoment H node1570 := by
  calc
    injectiveMoment H raw1538 = injectiveMoment H raw1538step0 := by
      have heq : raw1538step0 = (fun i j => raw1538 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1538 permutation39 permutation9
    _ = injectiveMoment H node1570 := by rfl

def raw1539 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1539step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1539 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1539 = injectiveMoment H node1571 := by
  calc
    injectiveMoment H raw1539 = injectiveMoment H raw1539step0 := by
      have heq : raw1539step0 = (fun i j => raw1539 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1539 permutation39 permutation9
    _ = injectiveMoment H node1571 := by rfl

def raw1540 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1540step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1540 = injectiveMoment H node915 := by
  calc
    injectiveMoment H raw1540 = injectiveMoment H raw1540step0 := by
      have hz : ∀ j, raw1540 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw1540step0 = (fun i j => raw1540 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1540 permutation80 hz
    injectiveMoment H raw1540step0 = injectiveMoment H raw1540step1 := by
      have heq : raw1540step1 = (fun i j => raw1540step0 (permutation13 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1540step0 permutation13 permutation17
    _ = injectiveMoment H node915 := by rfl

def raw1541 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1541 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw1541 = injectiveMoment H raw1541step0 := by
      have hz : ∀ j, raw1541 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw1541step0 = (fun i j => raw1541 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1541 permutation80 hz
    injectiveMoment H raw1541step0 = injectiveMoment H raw1541step1 := by
      have heq : raw1541step1 = (fun i j => raw1541step0 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1541step0 permutation10 permutation15
    _ = injectiveMoment H node769 := by rfl

def raw1542 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1542step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1542 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1542 = injectiveMoment H node910 := by
  calc
    injectiveMoment H raw1542 = injectiveMoment H raw1542step0 := by
      have hz : ∀ j, raw1542 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw1542step0 = (fun i j => raw1542 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1542 permutation80 hz
    injectiveMoment H raw1542step0 = injectiveMoment H raw1542step1 := by
      have heq : raw1542step1 = (fun i j => raw1542step0 (permutation11 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1542step0 permutation11 permutation17
    _ = injectiveMoment H node910 := by rfl

def raw1543 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, -1, -2]]

def raw1543step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 0, 1], ![-1, 1, 1, 0, -1], ![4, -1, -1, 0, -2]]

def raw1543step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![-1, 1, 1, -1], ![4, -1, -1, -2]]

def raw1543step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical1543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1543 = injectiveMoment H node907 := by
  calc
    injectiveMoment H raw1543 = injectiveMoment H raw1543step0 := by
      have heq : raw1543step0 = raw1543.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1543).symm
    injectiveMoment H raw1543step0 = injectiveMoment H raw1543step1 := by
      have hz : ∀ i, raw1543step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw1543step1 = (fun i j => raw1543step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1543step0 permutation104 hz
    injectiveMoment H raw1543step1 = injectiveMoment H raw1543step2 := by
      have heq : raw1543step2 = (fun i j => raw1543step1 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1543step1 permutation29 permutation18
    _ = injectiveMoment H node907 := by rfl

def raw1544 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 1, -2, -1]]

def raw1544step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -2, -1]]

theorem canonical1544 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1544 = injectiveMoment H node2389 := by
  calc
    injectiveMoment H raw1544 = injectiveMoment H raw1544step0 := by
      have heq : raw1544step0 = (fun i j => raw1544 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1544 permutation33 permutation15
    _ = injectiveMoment H node2389 := by rfl

def raw1545 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1545step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1545 = injectiveMoment H node2395 := by
  calc
    injectiveMoment H raw1545 = injectiveMoment H raw1545step0 := by
      have heq : raw1545step0 = (fun i j => raw1545 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1545 permutation34 permutation15
    _ = injectiveMoment H node2395 := by rfl

def raw1546 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1546step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical1546 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1546 = injectiveMoment H node2394 := by
  calc
    injectiveMoment H raw1546 = injectiveMoment H raw1546step0 := by
      have heq : raw1546step0 = (fun i j => raw1546 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1546 permutation34 permutation15
    _ = injectiveMoment H node2394 := by rfl

def raw1547 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1547step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical1547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1547 = injectiveMoment H node2393 := by
  calc
    injectiveMoment H raw1547 = injectiveMoment H raw1547step0 := by
      have heq : raw1547step0 = (fun i j => raw1547 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1547 permutation34 permutation15
    _ = injectiveMoment H node2393 := by rfl

def raw1548 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem canonical1548 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1548 = injectiveMoment H node1582 := by
  rfl

def raw1549 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw1549step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1549 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1549 = injectiveMoment H node1573 := by
  calc
    injectiveMoment H raw1549 = injectiveMoment H raw1549step0 := by
      have heq : raw1549step0 = (fun i j => raw1549 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1549 permutation45 permutation11
    _ = injectiveMoment H node1573 := by rfl

def raw1550 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

theorem canonical1550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1550 = injectiveMoment H node1583 := by
  rfl

def raw1551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical1551 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1551 = injectiveMoment H node1584 := by
  rfl

def raw1552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

theorem canonical1552 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1552 = injectiveMoment H node1585 := by
  rfl

def raw1553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

theorem canonical1553 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1553 = injectiveMoment H node1586 := by
  rfl

def raw1554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1554step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical1554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1554 = injectiveMoment H node2390 := by
  calc
    injectiveMoment H raw1554 = injectiveMoment H raw1554step0 := by
      have heq : raw1554step0 = (fun i j => raw1554 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1554 permutation33 permutation15
    _ = injectiveMoment H node2390 := by rfl

def raw1555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1555step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical1555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1555 = injectiveMoment H node2391 := by
  calc
    injectiveMoment H raw1555 = injectiveMoment H raw1555step0 := by
      have heq : raw1555step0 = (fun i j => raw1555 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1555 permutation33 permutation15
    _ = injectiveMoment H node2391 := by rfl

def raw1556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1556step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical1556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1556 = injectiveMoment H node2392 := by
  calc
    injectiveMoment H raw1556 = injectiveMoment H raw1556step0 := by
      have heq : raw1556step0 = (fun i j => raw1556 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1556 permutation33 permutation15
    _ = injectiveMoment H node2392 := by rfl

def raw1557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical1557 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1557 = injectiveMoment H node2392 := by
  calc
    injectiveMoment H raw1557 = injectiveMoment H raw1557step0 := by
      have heq : raw1557step0 = (fun i j => raw1557 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1557 permutation34 permutation15
    _ = injectiveMoment H node2392 := by rfl

def raw1558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 1, -1, -2]]

def raw1558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![-1, 1, 1, -1], ![4, -1, -1, -2]]

def raw1558step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical1558 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1558 = injectiveMoment H node907 := by
  calc
    injectiveMoment H raw1558 = injectiveMoment H raw1558step0 := by
      have heq : raw1558step0 = raw1558.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1558).symm
    injectiveMoment H raw1558step0 = injectiveMoment H raw1558step1 := by
      have heq : raw1558step1 = (fun i j => raw1558step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1558step0 permutation29 permutation18
    _ = injectiveMoment H node907 := by rfl

def raw1559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem canonical1559 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1559 = injectiveMoment H node1587 := by
  rfl

def raw1560 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

theorem canonical1560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1560 = injectiveMoment H node1588 := by
  rfl

def raw1561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, 0, -2]]

def raw1561step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1561 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1561 = injectiveMoment H node2395 := by
  calc
    injectiveMoment H raw1561 = injectiveMoment H raw1561step0 := by
      have heq : raw1561step0 = (fun i j => raw1561 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1561 permutation36 permutation15
    _ = injectiveMoment H node2395 := by rfl

def raw1562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, -1, -1]]

def raw1562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical1562 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1562 = injectiveMoment H node2398 := by
  calc
    injectiveMoment H raw1562 = injectiveMoment H raw1562step0 := by
      have heq : raw1562step0 = (fun i j => raw1562 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1562 permutation36 permutation15
    _ = injectiveMoment H node2398 := by rfl

def raw1563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem canonical1563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1563 = injectiveMoment H node1589 := by
  rfl

def raw1564 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw1564step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem canonical1564 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1564 = injectiveMoment H node1548 := by
  calc
    injectiveMoment H raw1564 = injectiveMoment H raw1564step0 := by
      have heq : raw1564step0 = (fun i j => raw1564 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1564 permutation41 permutation11
    _ = injectiveMoment H node1548 := by rfl

def raw1565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw1565step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1565 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1565 = injectiveMoment H node1557 := by
  calc
    injectiveMoment H raw1565 = injectiveMoment H raw1565step0 := by
      have heq : raw1565step0 = (fun i j => raw1565 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1565 permutation39 permutation11
    _ = injectiveMoment H node1557 := by rfl

def raw1566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw1566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical1566 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1566 = injectiveMoment H node1558 := by
  calc
    injectiveMoment H raw1566 = injectiveMoment H raw1566step0 := by
      have heq : raw1566step0 = (fun i j => raw1566 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1566 permutation39 permutation11
    _ = injectiveMoment H node1558 := by rfl

def raw1567 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw1567step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical1567 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1567 = injectiveMoment H node1559 := by
  calc
    injectiveMoment H raw1567 = injectiveMoment H raw1567step0 := by
      have heq : raw1567step0 = (fun i j => raw1567 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1567 permutation40 permutation11
    _ = injectiveMoment H node1559 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
