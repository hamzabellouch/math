import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw1504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![-1, 2, 0, -1], ![4, -1, -1, -2]]

def raw1504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1504 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1504 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw1504 = injectiveMoment H raw1504step0 := by
      have heq : raw1504step0 = raw1504.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1504).symm
    injectiveMoment H raw1504step0 = injectiveMoment H raw1504step1 := by
      have heq : raw1504step1 = (fun i j => raw1504step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1504step0 permutation30 permutation24
    _ = injectiveMoment H node896 := by rfl

def raw1505 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 2, -2, -1]]

theorem canonical1505 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1505 = injectiveMoment H node452 := by
  rfl

def raw1506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

theorem canonical1506 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1506 = injectiveMoment H node453 := by
  rfl

def raw1507 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical1507 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1507 = injectiveMoment H node454 := by
  rfl

def raw1508 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw1508step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical1508 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1508 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw1508 = injectiveMoment H raw1508step0 := by
      have heq : raw1508step0 = (fun i j => raw1508 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1508 permutation10 permutation9
    _ = injectiveMoment H node454 := by rfl

def raw1509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, 1, -3], ![1, 1, -2, 0]]

def raw1509step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

theorem canonical1509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1509 = injectiveMoment H node453 := by
  calc
    injectiveMoment H raw1509 = injectiveMoment H raw1509step0 := by
      have heq : raw1509step0 = (fun i j => raw1509 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1509 permutation10 permutation9
    _ = injectiveMoment H node453 := by rfl

def raw1510 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 2, -2, -1], ![1, 0, 1, -2]]

def raw1510step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 2, -2, -1]]

theorem canonical1510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1510 = injectiveMoment H node452 := by
  calc
    injectiveMoment H raw1510 = injectiveMoment H raw1510step0 := by
      have heq : raw1510step0 = (fun i j => raw1510 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1510 permutation10 permutation9
    _ = injectiveMoment H node452 := by rfl

def raw1511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 2, -1, -2], ![1, 0, 0, -1]]

def raw1511step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![-1, 2, -1, 0], ![4, -1, -2, -1]]

def raw1511step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1511 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw1511 = injectiveMoment H raw1511step0 := by
      have heq : raw1511step0 = raw1511.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1511).symm
    injectiveMoment H raw1511step0 = injectiveMoment H raw1511step1 := by
      have heq : raw1511step1 = (fun i j => raw1511step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1511step0 permutation30 permutation30
    _ = injectiveMoment H node896 := by rfl

def raw1512 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1512step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![-1, 3, -1, -1], ![4, -2, 0, -2]]

def raw1512step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, 1, -1, -1], ![1, -3, 1, 1], ![-4, 2, 0, 2]]

def raw1512step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 1, -3, 1]]

theorem canonical1512 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1512 = injectiveMoment H node1090 := by
  calc
    injectiveMoment H raw1512 = injectiveMoment H raw1512step0 := by
      have heq : raw1512step0 = raw1512.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1512).symm
    injectiveMoment H raw1512step0 = injectiveMoment H raw1512step1 := by
      have heq : raw1512step1 = -raw1512step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1512step0).symm
    injectiveMoment H raw1512step1 = injectiveMoment H raw1512step2 := by
      have heq : raw1512step2 = (fun i j => raw1512step1 (permutation16 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1512step1 permutation16 permutation26
    _ = injectiveMoment H node1090 := by rfl

def raw1513 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1513step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![-1, 3, 0, -2], ![4, -2, -1, -1]]

def raw1513step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 3, -2, -1], ![1, -1, 1, -1]]

theorem canonical1513 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1513 = injectiveMoment H node777 := by
  calc
    injectiveMoment H raw1513 = injectiveMoment H raw1513step0 := by
      have heq : raw1513step0 = raw1513.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1513).symm
    injectiveMoment H raw1513step0 = injectiveMoment H raw1513step1 := by
      have heq : raw1513step1 = (fun i j => raw1513step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1513step0 permutation28 permutation24
    _ = injectiveMoment H node777 := by rfl

def raw1514 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical1514 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1514 = injectiveMoment H node455 := by
  rfl

def raw1515 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical1515 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1515 = injectiveMoment H node456 := by
  rfl

def raw1516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical1516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1516 = injectiveMoment H node457 := by
  rfl

def raw1517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1517step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![-1, 3, -1, -1], ![4, -2, 0, -2]]

def raw1517step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, 0, -2], ![1, -3, 1, 1], ![-4, 2, 0, 2]]

def raw1517step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -3, 1]]

theorem canonical1517 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1517 = injectiveMoment H node988 := by
  calc
    injectiveMoment H raw1517 = injectiveMoment H raw1517step0 := by
      have heq : raw1517step0 = raw1517.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1517).symm
    injectiveMoment H raw1517step0 = injectiveMoment H raw1517step1 := by
      have heq : raw1517step1 = -raw1517step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1517step0).symm
    injectiveMoment H raw1517step1 = injectiveMoment H raw1517step2 := by
      have heq : raw1517step2 = (fun i j => raw1517step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1517step1 permutation10 permutation26
    _ = injectiveMoment H node988 := by rfl

def raw1518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![-1, 3, 0, -2], ![4, -2, -1, -1]]

def raw1518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 3, -2, -1], ![1, 0, 1, -2]]

theorem canonical1518 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1518 = injectiveMoment H node759 := by
  calc
    injectiveMoment H raw1518 = injectiveMoment H raw1518step0 := by
      have heq : raw1518step0 = raw1518.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1518).symm
    injectiveMoment H raw1518step0 = injectiveMoment H raw1518step1 := by
      have heq : raw1518step1 = (fun i j => raw1518step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1518step0 permutation30 permutation24
    _ = injectiveMoment H node759 := by rfl

def raw1519 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1519 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1519 = injectiveMoment H node458 := by
  rfl

def raw1520 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def raw1520step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

theorem canonical1520 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1520 = injectiveMoment H node1545 := by
  calc
    injectiveMoment H raw1520 = injectiveMoment H raw1520step0 := by
      have heq : raw1520step0 = (fun i j => raw1520 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1520 permutation34 permutation11
    _ = injectiveMoment H node1545 := by rfl

def raw1521 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw1521step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem canonical1521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1521 = injectiveMoment H node764 := by
  calc
    injectiveMoment H raw1521 = injectiveMoment H raw1521step0 := by
      have heq : raw1521step0 = (fun i j => raw1521 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1521 permutation10 permutation15
    _ = injectiveMoment H node764 := by rfl

def raw1522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1522step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1522 = injectiveMoment H node1546 := by
  calc
    injectiveMoment H raw1522 = injectiveMoment H raw1522step0 := by
      have heq : raw1522step0 = (fun i j => raw1522 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1522 permutation34 permutation11
    _ = injectiveMoment H node1546 := by rfl

def raw1523 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 1, -2]]

def raw1523step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, -1, 1, 1], ![4, 1, -3, -2]]

def raw1523step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -2, -3, 4]]

theorem canonical1523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1523 = injectiveMoment H node1364 := by
  calc
    injectiveMoment H raw1523 = injectiveMoment H raw1523step0 := by
      have heq : raw1523step0 = raw1523.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1523).symm
    injectiveMoment H raw1523step0 = injectiveMoment H raw1523step1 := by
      have heq : raw1523step1 = (fun i j => raw1523step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1523step0 permutation23 permutation20
    _ = injectiveMoment H node1364 := by rfl

def raw1524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1524step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![-1, 0, 0, -1, 2], ![4, 0, -1, 0, -3]]

def raw1524step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2], ![4, -1, 0, -3]]

def raw1524step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1524 = injectiveMoment H node1171 := by
  calc
    injectiveMoment H raw1524 = injectiveMoment H raw1524step0 := by
      have heq : raw1524step0 = raw1524.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1524).symm
    injectiveMoment H raw1524step0 = injectiveMoment H raw1524step1 := by
      have hz : ∀ i, raw1524step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1524step1 = (fun i j => raw1524step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1524step0 permutation57 hz
    injectiveMoment H raw1524step1 = injectiveMoment H raw1524step2 := by
      have heq : raw1524step2 = (fun i j => raw1524step1 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1524step1 permutation31 permutation18
    _ = injectiveMoment H node1171 := by rfl

def raw1525 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1525step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![4, 0, -2, -2]]

def raw1525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![4, -2, -2]]

def raw1525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical1525 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1525 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw1525 = injectiveMoment H raw1525step0 := by
      have heq : raw1525step0 = raw1525.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1525).symm
    injectiveMoment H raw1525step0 = injectiveMoment H raw1525step1 := by
      have hz : ∀ i, raw1525step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1525step1 = (fun i j => raw1525step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1525step0 permutation15 hz
    injectiveMoment H raw1525step1 = injectiveMoment H raw1525step2 := by
      have heq : raw1525step2 = (fun i j => raw1525step1 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1525step1 permutation30 permutation8
    _ = injectiveMoment H node145 := by rfl

def raw1526 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1526step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 0, -1, 2], ![4, 0, 0, -4]]

def raw1526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![4, 0, -4]]

def raw1526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

theorem canonical1526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1526 = injectiveMoment H node286 := by
  calc
    injectiveMoment H raw1526 = injectiveMoment H raw1526step0 := by
      have heq : raw1526step0 = raw1526.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1526).symm
    injectiveMoment H raw1526step0 = injectiveMoment H raw1526step1 := by
      have hz : ∀ i, raw1526step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1526step1 = (fun i j => raw1526step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1526step0 permutation15 hz
    injectiveMoment H raw1526step1 = injectiveMoment H raw1526step2 := by
      have heq : raw1526step2 = (fun i j => raw1526step1 (permutation24 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1526step1 permutation24 permutation5
    _ = injectiveMoment H node286 := by rfl

def raw1527 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1527step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 0, 1, 0], ![4, 0, -2, -2]]

def raw1527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![4, -2, -2]]

def raw1527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical1527 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1527 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw1527 = injectiveMoment H raw1527step0 := by
      have heq : raw1527step0 = raw1527.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1527).symm
    injectiveMoment H raw1527step0 = injectiveMoment H raw1527step1 := by
      have hz : ∀ i, raw1527step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1527step1 = (fun i j => raw1527step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1527step0 permutation15 hz
    injectiveMoment H raw1527step1 = injectiveMoment H raw1527step2 := by
      have heq : raw1527step2 = (fun i j => raw1527step1 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1527step1 permutation30 permutation6
    _ = injectiveMoment H node150 := by rfl

def raw1528 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1528step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 0, 2, -1], ![4, 0, -3, -1]]

def raw1528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![4, -3, -1]]

def raw1528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical1528 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1528 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw1528 = injectiveMoment H raw1528step0 := by
      have heq : raw1528step0 = raw1528.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1528).symm
    injectiveMoment H raw1528step0 = injectiveMoment H raw1528step1 := by
      have hz : ∀ i, raw1528step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1528step1 = (fun i j => raw1528step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1528step0 permutation15 hz
    injectiveMoment H raw1528step1 = injectiveMoment H raw1528step2 := by
      have heq : raw1528step2 = (fun i j => raw1528step1 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1528step1 permutation32 permutation8
    _ = injectiveMoment H node246 := by rfl

def raw1529 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1529step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem canonical1529 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1529 = injectiveMoment H node1548 := by
  calc
    injectiveMoment H raw1529 = injectiveMoment H raw1529step0 := by
      have heq : raw1529step0 = (fun i j => raw1529 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1529 permutation39 permutation9
    _ = injectiveMoment H node1548 := by rfl

def raw1530 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1530step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

theorem canonical1530 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1530 = injectiveMoment H node1551 := by
  calc
    injectiveMoment H raw1530 = injectiveMoment H raw1530step0 := by
      have heq : raw1530step0 = (fun i j => raw1530 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1530 permutation39 permutation9
    _ = injectiveMoment H node1551 := by rfl

def raw1531 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw1531step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

theorem canonical1531 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1531 = injectiveMoment H node1552 := by
  calc
    injectiveMoment H raw1531 = injectiveMoment H raw1531step0 := by
      have heq : raw1531step0 = (fun i j => raw1531 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1531 permutation39 permutation9
    _ = injectiveMoment H node1552 := by rfl

def raw1532 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1532step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem canonical1532 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1532 = injectiveMoment H node1564 := by
  calc
    injectiveMoment H raw1532 = injectiveMoment H raw1532step0 := by
      have heq : raw1532step0 = (fun i j => raw1532 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1532 permutation39 permutation9
    _ = injectiveMoment H node1564 := by rfl

def raw1533 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1533step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical1533 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1533 = injectiveMoment H node1565 := by
  calc
    injectiveMoment H raw1533 = injectiveMoment H raw1533step0 := by
      have heq : raw1533step0 = (fun i j => raw1533 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1533 permutation39 permutation9
    _ = injectiveMoment H node1565 := by rfl

def raw1534 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1534step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical1534 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1534 = injectiveMoment H node1566 := by
  calc
    injectiveMoment H raw1534 = injectiveMoment H raw1534step0 := by
      have heq : raw1534step0 = (fun i j => raw1534 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1534 permutation39 permutation9
    _ = injectiveMoment H node1566 := by rfl

def raw1535 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1535step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical1535 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1535 = injectiveMoment H node1567 := by
  calc
    injectiveMoment H raw1535 = injectiveMoment H raw1535step0 := by
      have heq : raw1535step0 = (fun i j => raw1535 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1535 permutation39 permutation9
    _ = injectiveMoment H node1567 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
