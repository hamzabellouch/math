import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8544 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8544 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8544 = injectiveMoment H node2464 := by
  calc
    injectiveMoment H raw8544 = injectiveMoment H raw8544step0 := by
      have heq : raw8544step0 = (fun i j => raw8544 (permutation279 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8544 permutation279 permutation4
    _ = injectiveMoment H node2464 := by rfl

def raw8545 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![1, -1, 0]]

def raw8545step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8545 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw8545 = injectiveMoment H raw8545step0 := by
      have heq : raw8545step0 = (fun i j => raw8545 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8545 permutation5 permutation4
    _ = injectiveMoment H node61 := by rfl

def raw8546 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1]]

def raw8546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8546 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8546 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw8546 = injectiveMoment H raw8546step0 := by
      have heq : raw8546step0 = (fun i j => raw8546 (permutation15 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8546 permutation15 permutation4
    _ = injectiveMoment H node272 := by rfl

def raw8547 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 4, -3], ![0, -3, 3], ![1, 0, -1]]

def raw8547step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical8547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8547 = injectiveMoment H node255 := by
  calc
    injectiveMoment H raw8547 = injectiveMoment H raw8547step0 := by
      have heq : raw8547step0 = (fun i j => raw8547 (permutation15 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8547 permutation15 permutation4
    _ = injectiveMoment H node255 := by rfl

def raw8548 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, -3, 3], ![0, 4, -4]]

def raw8548step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![4, -4]]

def raw8548step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical8548 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8548 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw8548 = injectiveMoment H raw8548step0 := by
      have hz : ∀ i, raw8548 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8548step0 = (fun i j => raw8548 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8548 permutation3 hz
    injectiveMoment H raw8548step0 = injectiveMoment H raw8548step1 := by
      have heq : raw8548step1 = (fun i j => raw8548step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8548step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

def raw8549 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def raw8549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![-2, -1, 3]]

def raw8549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical8549 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8549 = injectiveMoment H node1881 := by
  calc
    injectiveMoment H raw8549 = injectiveMoment H raw8549step0 := by
      have heq : raw8549step0 = -raw8549 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8549).symm
    injectiveMoment H raw8549step0 = injectiveMoment H raw8549step1 := by
      have heq : raw8549step1 = (fun i j => raw8549step0 (permutation375 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8549step0 permutation375 permutation3
    _ = injectiveMoment H node1881 := by rfl

def raw8550 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def raw8550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8550 = injectiveMoment H node1543 := by
  calc
    injectiveMoment H raw8550 = injectiveMoment H raw8550step0 := by
      have heq : raw8550step0 = (fun i j => raw8550 (permutation314 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8550 permutation314 permutation4
    _ = injectiveMoment H node1543 := by rfl

def raw8551 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2], ![-3, 0, 3]]

def raw8551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

theorem canonical8551 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8551 = injectiveMoment H node1398 := by
  calc
    injectiveMoment H raw8551 = injectiveMoment H raw8551step0 := by
      have heq : raw8551step0 = -raw8551 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8551).symm
    injectiveMoment H raw8551step0 = injectiveMoment H raw8551step1 := by
      have heq : raw8551step1 = (fun i j => raw8551step0 (permutation363 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8551step0 permutation363 permutation3
    _ = injectiveMoment H node1398 := by rfl

def raw8552 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def raw8552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8552 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8552 = injectiveMoment H node1874 := by
  calc
    injectiveMoment H raw8552 = injectiveMoment H raw8552step0 := by
      have heq : raw8552step0 = -raw8552 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8552).symm
    injectiveMoment H raw8552step0 = injectiveMoment H raw8552step1 := by
      have heq : raw8552step1 = (fun i j => raw8552step0 (permutation363 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8552step0 permutation363 permutation3
    _ = injectiveMoment H node1874 := by rfl

def raw8553 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def raw8553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8553 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8553 = injectiveMoment H node2126 := by
  calc
    injectiveMoment H raw8553 = injectiveMoment H raw8553step0 := by
      have heq : raw8553step0 = -raw8553 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8553).symm
    injectiveMoment H raw8553step0 = injectiveMoment H raw8553step1 := by
      have heq : raw8553step1 = (fun i j => raw8553step0 (permutation363 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8553step0 permutation363 permutation3
    _ = injectiveMoment H node2126 := by rfl

def raw8554 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def raw8554step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw8554step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8554 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw8554 = injectiveMoment H raw8554step0 := by
      have hz : ∀ i, raw8554 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8554step0 = (fun i j => raw8554 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8554 permutation3 hz
    injectiveMoment H raw8554step0 = injectiveMoment H raw8554step1 := by
      have heq : raw8554step1 = (fun i j => raw8554step0 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8554step0 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw8555 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8555 = injectiveMoment H node2113 := by
  calc
    injectiveMoment H raw8555 = injectiveMoment H raw8555step0 := by
      have heq : raw8555step0 = (fun i j => raw8555 (permutation277 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8555 permutation277 permutation3
    _ = injectiveMoment H node2113 := by rfl

def raw8556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def raw8556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

theorem canonical8556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8556 = injectiveMoment H node1414 := by
  calc
    injectiveMoment H raw8556 = injectiveMoment H raw8556step0 := by
      have heq : raw8556step0 = (fun i j => raw8556 (permutation277 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8556 permutation277 permutation3
    _ = injectiveMoment H node1414 := by rfl

def raw8557 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def raw8557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8557 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8557 = injectiveMoment H node2114 := by
  calc
    injectiveMoment H raw8557 = injectiveMoment H raw8557step0 := by
      have heq : raw8557step0 = (fun i j => raw8557 (permutation277 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8557 permutation277 permutation3
    _ = injectiveMoment H node2114 := by rfl

def raw8558 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8558 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8558 = injectiveMoment H node2139 := by
  calc
    injectiveMoment H raw8558 = injectiveMoment H raw8558step0 := by
      have heq : raw8558step0 = (fun i j => raw8558 (permutation355 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8558 permutation355 permutation4
    _ = injectiveMoment H node2139 := by rfl

def raw8559 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def raw8559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

theorem canonical8559 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8559 = injectiveMoment H node1435 := by
  calc
    injectiveMoment H raw8559 = injectiveMoment H raw8559step0 := by
      have heq : raw8559step0 = (fun i j => raw8559 (permutation331 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8559 permutation331 permutation3
    _ = injectiveMoment H node1435 := by rfl

def raw8560 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 3, -3]]

def raw8560step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw8560step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8560 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8560 = injectiveMoment H raw8560step0 := by
      have hz : ∀ i, raw8560 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8560step0 = (fun i j => raw8560 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8560 permutation3 hz
    injectiveMoment H raw8560step0 = injectiveMoment H raw8560step1 := by
      have heq : raw8560step1 = (fun i j => raw8560step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8560step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw8561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def raw8561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8561 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8561 = injectiveMoment H node2117 := by
  calc
    injectiveMoment H raw8561 = injectiveMoment H raw8561step0 := by
      have heq : raw8561step0 = (fun i j => raw8561 (permutation279 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8561 permutation279 permutation3
    _ = injectiveMoment H node2117 := by rfl

def raw8562 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def raw8562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8562 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8562 = injectiveMoment H node2298 := by
  calc
    injectiveMoment H raw8562 = injectiveMoment H raw8562step0 := by
      have heq : raw8562step0 = (fun i j => raw8562 (permutation295 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8562 permutation295 permutation4
    _ = injectiveMoment H node2298 := by rfl

def raw8563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def raw8563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8563 = injectiveMoment H node1416 := by
  calc
    injectiveMoment H raw8563 = injectiveMoment H raw8563step0 := by
      have heq : raw8563step0 = (fun i j => raw8563 (permutation277 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8563 permutation277 permutation3
    _ = injectiveMoment H node1416 := by rfl

def raw8564 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def raw8564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8564 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8564 = injectiveMoment H node2116 := by
  calc
    injectiveMoment H raw8564 = injectiveMoment H raw8564step0 := by
      have heq : raw8564step0 = (fun i j => raw8564 (permutation279 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8564 permutation279 permutation3
    _ = injectiveMoment H node2116 := by rfl

def raw8565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def raw8565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8565 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8565 = injectiveMoment H node2672 := by
  calc
    injectiveMoment H raw8565 = injectiveMoment H raw8565step0 := by
      have heq : raw8565step0 = (fun i j => raw8565 (permutation298 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8565 permutation298 permutation3
    _ = injectiveMoment H node2672 := by rfl

def raw8566 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def raw8566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]

def raw8566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

theorem canonical8566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8566 = injectiveMoment H node1410 := by
  calc
    injectiveMoment H raw8566 = injectiveMoment H raw8566step0 := by
      have heq : raw8566step0 = -raw8566 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8566).symm
    injectiveMoment H raw8566step0 = injectiveMoment H raw8566step1 := by
      have heq : raw8566step1 = (fun i j => raw8566step0 (permutation366 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8566step0 permutation366 permutation6
    _ = injectiveMoment H node1410 := by rfl

def raw8567 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def raw8567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![1, -3, 2], ![-2, -1, 3]]

def raw8567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

theorem canonical8567 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8567 = injectiveMoment H node1889 := by
  calc
    injectiveMoment H raw8567 = injectiveMoment H raw8567step0 := by
      have heq : raw8567step0 = -raw8567 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8567).symm
    injectiveMoment H raw8567step0 = injectiveMoment H raw8567step1 := by
      have heq : raw8567step1 = (fun i j => raw8567step0 (permutation311 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8567step0 permutation311 permutation3
    _ = injectiveMoment H node1889 := by rfl

def raw8568 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0]]

def raw8568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical8568 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8568 = injectiveMoment H node1150 := by
  calc
    injectiveMoment H raw8568 = injectiveMoment H raw8568step0 := by
      have heq : raw8568step0 = (fun i j => raw8568 (permutation80 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8568 permutation80 permutation3
    _ = injectiveMoment H node1150 := by rfl

def raw8569 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def raw8569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]

def raw8569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical8569 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8569 = injectiveMoment H node1862 := by
  calc
    injectiveMoment H raw8569 = injectiveMoment H raw8569step0 := by
      have heq : raw8569step0 = -raw8569 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8569).symm
    injectiveMoment H raw8569step0 = injectiveMoment H raw8569step1 := by
      have heq : raw8569step1 = (fun i j => raw8569step0 (permutation373 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8569step0 permutation373 permutation3
    _ = injectiveMoment H node1862 := by rfl

def raw8570 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def raw8570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8570 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8570 = injectiveMoment H node2382 := by
  calc
    injectiveMoment H raw8570 = injectiveMoment H raw8570step0 := by
      have heq : raw8570step0 = (fun i j => raw8570 (permutation356 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8570 permutation356 permutation4
    _ = injectiveMoment H node2382 := by rfl

def raw8571 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def raw8571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8571 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8571 = injectiveMoment H node2671 := by
  calc
    injectiveMoment H raw8571 = injectiveMoment H raw8571step0 := by
      have heq : raw8571step0 = (fun i j => raw8571 (permutation235 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8571 permutation235 permutation3
    _ = injectiveMoment H node2671 := by rfl

def raw8572 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def raw8572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical8572 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8572 = injectiveMoment H node1532 := by
  calc
    injectiveMoment H raw8572 = injectiveMoment H raw8572step0 := by
      have heq : raw8572step0 = (fun i j => raw8572 (permutation355 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8572 permutation355 permutation4
    _ = injectiveMoment H node1532 := by rfl

def raw8573 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw8573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8573 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8573 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw8573 = injectiveMoment H raw8573step0 := by
      have heq : raw8573step0 = (fun i j => raw8573 (permutation92 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8573 permutation92 permutation4
    _ = injectiveMoment H node1294 := by rfl

def raw8574 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0]]

def raw8574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8574 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8574 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H raw8574 = injectiveMoment H raw8574step0 := by
      have heq : raw8574step0 = (fun i j => raw8574 (permutation92 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8574 permutation92 permutation4
    _ = injectiveMoment H node1291 := by rfl

def raw8575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def raw8575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![-2, -2, 4]]

def raw8575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem canonical8575 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8575 = injectiveMoment H node1529 := by
  calc
    injectiveMoment H raw8575 = injectiveMoment H raw8575step0 := by
      have heq : raw8575step0 = -raw8575 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8575).symm
    injectiveMoment H raw8575step0 = injectiveMoment H raw8575step1 := by
      have heq : raw8575step1 = (fun i j => raw8575step0 (permutation373 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8575step0 permutation373 permutation3
    _ = injectiveMoment H node1529 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
