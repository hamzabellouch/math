import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw640 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical640 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw640 = injectiveMoment H node658 := by
  calc
    injectiveMoment H raw640 = injectiveMoment H raw640step0 := by
      have heq : raw640step0 = (fun i j => raw640 (permutation142 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw640 permutation142 permutation6
    _ = injectiveMoment H node658 := by rfl

def raw641 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]

def raw641step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw641 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw641 = injectiveMoment H raw641step0 := by
      have heq : raw641step0 = (fun i j => raw641 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw641 permutation30 permutation6
    _ = injectiveMoment H node180 := by rfl

def raw642 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]

def raw642step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw642 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw642 = injectiveMoment H raw642step0 := by
      have heq : raw642step0 = (fun i j => raw642 (permutation24 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw642 permutation24 permutation6
    _ = injectiveMoment H node209 := by rfl

def raw643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical643 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw643 = injectiveMoment H node1873 := by
  calc
    injectiveMoment H raw643 = injectiveMoment H raw643step0 := by
      have heq : raw643step0 = (fun i j => raw643 (permutation392 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw643 permutation392 permutation8
    _ = injectiveMoment H node1873 := by rfl

def raw644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical644 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw644 = injectiveMoment H node1874 := by
  calc
    injectiveMoment H raw644 = injectiveMoment H raw644step0 := by
      have heq : raw644step0 = -raw644 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw644).symm
    injectiveMoment H raw644step0 = injectiveMoment H raw644step1 := by
      have heq : raw644step1 = (fun i j => raw644step0 (permutation151 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw644step0 permutation151 permutation8
    _ = injectiveMoment H node1874 := by rfl

def raw645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical645 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw645 = injectiveMoment H node1877 := by
  calc
    injectiveMoment H raw645 = injectiveMoment H raw645step0 := by
      have heq : raw645step0 = -raw645 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw645).symm
    injectiveMoment H raw645step0 = injectiveMoment H raw645step1 := by
      have heq : raw645step1 = (fun i j => raw645step0 (permutation153 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw645step0 permutation153 permutation8
    _ = injectiveMoment H node1877 := by rfl

def raw646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw646 = injectiveMoment H node1861 := by
  calc
    injectiveMoment H raw646 = injectiveMoment H raw646step0 := by
      have heq : raw646step0 = (fun i j => raw646 (permutation372 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw646 permutation372 permutation6
    _ = injectiveMoment H node1861 := by rfl

def raw647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical647 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw647 = injectiveMoment H node2463 := by
  calc
    injectiveMoment H raw647 = injectiveMoment H raw647step0 := by
      have heq : raw647step0 = -raw647 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw647).symm
    injectiveMoment H raw647step0 = injectiveMoment H raw647step1 := by
      have heq : raw647step1 = (fun i j => raw647step0 (permutation164 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw647step0 permutation164 permutation6
    _ = injectiveMoment H node2463 := by rfl

def raw648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical648 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw648 = injectiveMoment H node2462 := by
  calc
    injectiveMoment H raw648 = injectiveMoment H raw648step0 := by
      have heq : raw648step0 = -raw648 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw648).symm
    injectiveMoment H raw648step0 = injectiveMoment H raw648step1 := by
      have heq : raw648step1 = (fun i j => raw648step0 (permutation158 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw648step0 permutation158 permutation6
    _ = injectiveMoment H node2462 := by rfl

def raw649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical649 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw649 = injectiveMoment H node1860 := by
  calc
    injectiveMoment H raw649 = injectiveMoment H raw649step0 := by
      have heq : raw649step0 = -raw649 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw649).symm
    injectiveMoment H raw649step0 = injectiveMoment H raw649step1 := by
      have heq : raw649step1 = (fun i j => raw649step0 (permutation168 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw649step0 permutation168 permutation8
    _ = injectiveMoment H node1860 := by rfl

def raw650 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]

def raw650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]

def raw650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical650 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw650 = injectiveMoment H node531 := by
  calc
    injectiveMoment H raw650 = injectiveMoment H raw650step0 := by
      have heq : raw650step0 = -raw650 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw650).symm
    injectiveMoment H raw650step0 = injectiveMoment H raw650step1 := by
      have heq : raw650step1 = (fun i j => raw650step0 (permutation40 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw650step0 permutation40 permutation8
    _ = injectiveMoment H node531 := by rfl

def raw651 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]

def raw651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw651 = injectiveMoment H node355 := by
  calc
    injectiveMoment H raw651 = injectiveMoment H raw651step0 := by
      have heq : raw651step0 = (fun i j => raw651 (permutation148 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw651 permutation148 permutation8
    _ = injectiveMoment H node355 := by rfl

def raw652 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]

def raw652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]

def raw652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical652 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw652 = injectiveMoment H node863 := by
  calc
    injectiveMoment H raw652 = injectiveMoment H raw652step0 := by
      have heq : raw652step0 = -raw652 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw652).symm
    injectiveMoment H raw652step0 = injectiveMoment H raw652step1 := by
      have heq : raw652step1 = (fun i j => raw652step0 (permutation37 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw652step0 permutation37 permutation6
    _ = injectiveMoment H node863 := by rfl

def raw653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical653 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw653 = injectiveMoment H node1885 := by
  calc
    injectiveMoment H raw653 = injectiveMoment H raw653step0 := by
      have heq : raw653step0 = -raw653 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw653).symm
    injectiveMoment H raw653step0 = injectiveMoment H raw653step1 := by
      have heq : raw653step1 = (fun i j => raw653step0 (permutation160 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw653step0 permutation160 permutation8
    _ = injectiveMoment H node1885 := by rfl

def raw654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]

def raw654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw654 = injectiveMoment H node1425 := by
  calc
    injectiveMoment H raw654 = injectiveMoment H raw654step0 := by
      have heq : raw654step0 = (fun i j => raw654 (permutation394 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw654 permutation394 permutation6
    _ = injectiveMoment H node1425 := by rfl

def raw655 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]

def raw655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical655 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw655 = injectiveMoment H node360 := by
  calc
    injectiveMoment H raw655 = injectiveMoment H raw655step0 := by
      have heq : raw655step0 = (fun i j => raw655 (permutation127 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw655 permutation127 permutation6
    _ = injectiveMoment H node360 := by rfl

def raw656 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical656 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw656 = injectiveMoment H node561 := by
  calc
    injectiveMoment H raw656 = injectiveMoment H raw656step0 := by
      have heq : raw656step0 = -raw656 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw656).symm
    injectiveMoment H raw656step0 = injectiveMoment H raw656step1 := by
      have heq : raw656step1 = (fun i j => raw656step0 (permutation35 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw656step0 permutation35 permutation8
    _ = injectiveMoment H node561 := by rfl

def raw657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical657 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw657 = injectiveMoment H node1866 := by
  calc
    injectiveMoment H raw657 = injectiveMoment H raw657step0 := by
      have heq : raw657step0 = -raw657 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw657).symm
    injectiveMoment H raw657step0 = injectiveMoment H raw657step1 := by
      have heq : raw657step1 = (fun i j => raw657step0 (permutation166 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw657step0 permutation166 permutation8
    _ = injectiveMoment H node1866 := by rfl

def raw658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw658 = injectiveMoment H node2303 := by
  calc
    injectiveMoment H raw658 = injectiveMoment H raw658step0 := by
      have heq : raw658step0 = (fun i j => raw658 (permutation232 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw658 permutation232 permutation6
    _ = injectiveMoment H node2303 := by rfl

def raw659 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]

def raw659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical659 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw659 = injectiveMoment H node702 := by
  calc
    injectiveMoment H raw659 = injectiveMoment H raw659step0 := by
      have heq : raw659step0 = (fun i j => raw659 (permutation103 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw659 permutation103 permutation6
    _ = injectiveMoment H node702 := by rfl

def raw660 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical660 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw660 = injectiveMoment H node535 := by
  calc
    injectiveMoment H raw660 = injectiveMoment H raw660step0 := by
      have heq : raw660step0 = -raw660 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw660).symm
    injectiveMoment H raw660step0 = injectiveMoment H raw660step1 := by
      have heq : raw660step1 = (fun i j => raw660step0 (permutation40 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw660step0 permutation40 permutation8
    _ = injectiveMoment H node535 := by rfl

def raw661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical661 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw661 = injectiveMoment H node1880 := by
  calc
    injectiveMoment H raw661 = injectiveMoment H raw661step0 := by
      have heq : raw661step0 = -raw661 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw661).symm
    injectiveMoment H raw661step0 = injectiveMoment H raw661step1 := by
      have heq : raw661step1 = (fun i j => raw661step0 (permutation151 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw661step0 permutation151 permutation8
    _ = injectiveMoment H node1880 := by rfl

def raw662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical662 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw662 = injectiveMoment H node1884 := by
  calc
    injectiveMoment H raw662 = injectiveMoment H raw662step0 := by
      have heq : raw662step0 = -raw662 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw662).symm
    injectiveMoment H raw662step0 = injectiveMoment H raw662step1 := by
      have heq : raw662step1 = (fun i j => raw662step0 (permutation151 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw662step0 permutation151 permutation8
    _ = injectiveMoment H node1884 := by rfl

def raw663 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical663 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw663 = injectiveMoment H node555 := by
  calc
    injectiveMoment H raw663 = injectiveMoment H raw663step0 := by
      have heq : raw663step0 = -raw663 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw663).symm
    injectiveMoment H raw663step0 = injectiveMoment H raw663step1 := by
      have heq : raw663step1 = (fun i j => raw663step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw663step0 permutation33 permutation8
    _ = injectiveMoment H node555 := by rfl

def raw664 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical664 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw664 = injectiveMoment H node560 := by
  calc
    injectiveMoment H raw664 = injectiveMoment H raw664step0 := by
      have heq : raw664step0 = -raw664 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw664).symm
    injectiveMoment H raw664step0 = injectiveMoment H raw664step1 := by
      have heq : raw664step1 = (fun i j => raw664step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw664step0 permutation33 permutation8
    _ = injectiveMoment H node560 := by rfl

def raw665 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical665 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw665 = injectiveMoment H node556 := by
  calc
    injectiveMoment H raw665 = injectiveMoment H raw665step0 := by
      have heq : raw665step0 = -raw665 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw665).symm
    injectiveMoment H raw665step0 = injectiveMoment H raw665step1 := by
      have heq : raw665step1 = (fun i j => raw665step0 (permutation34 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw665step0 permutation34 permutation8
    _ = injectiveMoment H node556 := by rfl

def raw666 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw666step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical666 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw666 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw666 = injectiveMoment H raw666step0 := by
      have heq : raw666step0 = (fun i j => raw666 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw666 permutation32 permutation8
    _ = injectiveMoment H node168 := by rfl

def raw667 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical667 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw667 = injectiveMoment H node562 := by
  calc
    injectiveMoment H raw667 = injectiveMoment H raw667step0 := by
      have heq : raw667step0 = -raw667 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw667).symm
    injectiveMoment H raw667step0 = injectiveMoment H raw667step1 := by
      have heq : raw667step1 = (fun i j => raw667step0 (permutation37 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw667step0 permutation37 permutation8
    _ = injectiveMoment H node562 := by rfl

def raw668 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]

def raw668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw668 = injectiveMoment H node371 := by
  calc
    injectiveMoment H raw668 = injectiveMoment H raw668step0 := by
      have heq : raw668step0 = (fun i j => raw668 (permutation144 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw668 permutation144 permutation6
    _ = injectiveMoment H node371 := by rfl

def raw669 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw669step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw669 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw669 = injectiveMoment H raw669step0 := by
      have heq : raw669step0 = (fun i j => raw669 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw669 permutation32 permutation6
    _ = injectiveMoment H node174 := by rfl

def raw670 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]

def raw670step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

theorem canonical670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw670 = injectiveMoment H node108 := by
  calc
    injectiveMoment H raw670 = injectiveMoment H raw670step0 := by
      have heq : raw670step0 = (fun i j => raw670 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw670 permutation30 permutation8
    _ = injectiveMoment H node108 := by rfl

def raw671 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw671step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw671 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw671 = injectiveMoment H raw671step0 := by
      have heq : raw671step0 = -raw671 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw671).symm
    injectiveMoment H raw671step0 = injectiveMoment H raw671step1 := by
      have heq : raw671step1 = (fun i j => raw671step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw671step0 permutation9 permutation8
    _ = injectiveMoment H node169 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
