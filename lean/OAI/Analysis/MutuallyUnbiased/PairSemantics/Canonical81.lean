import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2592 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2592step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2592step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical2592 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2592 = injectiveMoment H node1786 := by
  calc
    injectiveMoment H raw2592 = injectiveMoment H raw2592step0 := by
      have heq : raw2592step0 = -raw2592 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2592).symm
    injectiveMoment H raw2592step0 = injectiveMoment H raw2592step1 := by
      have heq : raw2592step1 = (fun i j => raw2592step0 (permutation48 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2592step0 permutation48 permutation26
    _ = injectiveMoment H node1786 := by rfl

def raw2593 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw2593step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 1, 0, 0]]

def raw2593step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical2593 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2593 = injectiveMoment H node1786 := by
  calc
    injectiveMoment H raw2593 = injectiveMoment H raw2593step0 := by
      have heq : raw2593step0 = -raw2593 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2593).symm
    injectiveMoment H raw2593step0 = injectiveMoment H raw2593step1 := by
      have heq : raw2593step1 = (fun i j => raw2593step0 (permutation54 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2593step0 permutation54 permutation26
    _ = injectiveMoment H node1786 := by rfl

def raw2594 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2594step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![1, 1, -1, -1]]

def raw2594step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical2594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2594 = injectiveMoment H node1112 := by
  calc
    injectiveMoment H raw2594 = injectiveMoment H raw2594step0 := by
      have heq : raw2594step0 = raw2594.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2594).symm
    injectiveMoment H raw2594step0 = injectiveMoment H raw2594step1 := by
      have heq : raw2594step1 = (fun i j => raw2594step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2594step0 permutation31 permutation26
    _ = injectiveMoment H node1112 := by rfl

def raw2595 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2595step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2595 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2595 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw2595 = injectiveMoment H raw2595step0 := by
      have heq : raw2595step0 = (fun i j => raw2595 (permutation11 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2595 permutation11 permutation10
    _ = injectiveMoment H node510 := by rfl

def raw2596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical2596 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2596 = injectiveMoment H node515 := by
  calc
    injectiveMoment H raw2596 = injectiveMoment H raw2596step0 := by
      have heq : raw2596step0 = (fun i j => raw2596 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2596 permutation9 permutation10
    _ = injectiveMoment H node515 := by rfl

def raw2597 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2597step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -2, 0, 0], ![1, 1, 0, -2]]

def raw2597step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-2, 2, 0, 0], ![-1, -1, 0, 2]]

def raw2597step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical2597 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2597 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw2597 = injectiveMoment H raw2597step0 := by
      have heq : raw2597step0 = raw2597.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2597).symm
    injectiveMoment H raw2597step0 = injectiveMoment H raw2597step1 := by
      have heq : raw2597step1 = -raw2597step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2597step0).symm
    injectiveMoment H raw2597step1 = injectiveMoment H raw2597step2 := by
      have heq : raw2597step2 = (fun i j => raw2597step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2597step1 permutation12 permutation26
    _ = injectiveMoment H node1058 := by rfl

def raw2598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2598step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![2, -2, 0, 0], ![1, 1, -1, -1]]

def raw2598step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![-1, -1, 1, 1]]

def raw2598step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2598 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2598 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw2598 = injectiveMoment H raw2598step0 := by
      have heq : raw2598step0 = raw2598.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2598).symm
    injectiveMoment H raw2598step0 = injectiveMoment H raw2598step1 := by
      have heq : raw2598step1 = -raw2598step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2598step0).symm
    injectiveMoment H raw2598step1 = injectiveMoment H raw2598step2 := by
      have heq : raw2598step2 = (fun i j => raw2598step1 (permutation9 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2598step1 permutation9 permutation26
    _ = injectiveMoment H node1040 := by rfl

def raw2599 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2599step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

theorem canonical2599 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2599 = injectiveMoment H node1829 := by
  calc
    injectiveMoment H raw2599 = injectiveMoment H raw2599step0 := by
      have heq : raw2599step0 = (fun i j => raw2599 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2599 permutation33 permutation10
    _ = injectiveMoment H node1829 := by rfl

def raw2600 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2600step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2600step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical2600 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2600 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw2600 = injectiveMoment H raw2600step0 := by
      have heq : raw2600step0 = -raw2600 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2600).symm
    injectiveMoment H raw2600step0 = injectiveMoment H raw2600step1 := by
      have heq : raw2600step1 = (fun i j => raw2600step0 (permutation45 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2600step0 permutation45 permutation32
    _ = injectiveMoment H node2448 := by rfl

def raw2601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -1, -1, 0], ![1, 0, 0, -1]]

def raw2601step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2601 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2601 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw2601 = injectiveMoment H raw2601step0 := by
      have heq : raw2601step0 = raw2601.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2601).symm
    injectiveMoment H raw2601step0 = injectiveMoment H raw2601step1 := by
      have heq : raw2601step1 = (fun i j => raw2601step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2601step0 permutation25 permutation18
    _ = injectiveMoment H node1040 := by rfl

def raw2602 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2602step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2602 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2602 = injectiveMoment H node1825 := by
  calc
    injectiveMoment H raw2602 = injectiveMoment H raw2602step0 := by
      have heq : raw2602step0 = (fun i j => raw2602 (permutation39 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2602 permutation39 permutation10
    _ = injectiveMoment H node1825 := by rfl

def raw2603 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2603step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2603step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical2603 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2603 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw2603 = injectiveMoment H raw2603step0 := by
      have heq : raw2603step0 = -raw2603 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2603).symm
    injectiveMoment H raw2603step0 = injectiveMoment H raw2603step1 := by
      have heq : raw2603step1 = (fun i j => raw2603step0 (permutation46 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2603step0 permutation46 permutation32
    _ = injectiveMoment H node2449 := by rfl

def raw2604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -1, 0, -1], ![1, 0, -1, 0]]

def raw2604step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![-1, 0, 1, 0]]

def raw2604step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2604 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2604 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw2604 = injectiveMoment H raw2604step0 := by
      have heq : raw2604step0 = raw2604.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2604).symm
    injectiveMoment H raw2604step0 = injectiveMoment H raw2604step1 := by
      have heq : raw2604step1 = -raw2604step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2604step0).symm
    injectiveMoment H raw2604step1 = injectiveMoment H raw2604step2 := by
      have heq : raw2604step2 = (fun i j => raw2604step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2604step1 permutation16 permutation18
    _ = injectiveMoment H node1110 := by rfl

def raw2605 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2605step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2605 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2605 = injectiveMoment H node1819 := by
  calc
    injectiveMoment H raw2605 = injectiveMoment H raw2605step0 := by
      have heq : raw2605step0 = (fun i j => raw2605 (permutation39 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2605 permutation39 permutation10
    _ = injectiveMoment H node1819 := by rfl

def raw2606 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw2606step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -1, 1, -2], ![1, 0, -2, 1]]

def raw2606step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-2, 1, -1, 2], ![-1, 0, 2, -1]]

def raw2606step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical2606 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2606 = injectiveMoment H node1111 := by
  calc
    injectiveMoment H raw2606 = injectiveMoment H raw2606step0 := by
      have heq : raw2606step0 = raw2606.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2606).symm
    injectiveMoment H raw2606step0 = injectiveMoment H raw2606step1 := by
      have heq : raw2606step1 = -raw2606step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2606step0).symm
    injectiveMoment H raw2606step1 = injectiveMoment H raw2606step2 := by
      have heq : raw2606step2 = (fun i j => raw2606step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2606step1 permutation16 permutation18
    _ = injectiveMoment H node1111 := by rfl

def raw2607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw2607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -1, -2, 1], ![1, 0, 2, -3]]

def raw2607step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical2607 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2607 = injectiveMoment H node851 := by
  calc
    injectiveMoment H raw2607 = injectiveMoment H raw2607step0 := by
      have heq : raw2607step0 = raw2607.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2607).symm
    injectiveMoment H raw2607step0 = injectiveMoment H raw2607step1 := by
      have heq : raw2607step1 = (fun i j => raw2607step0 (permutation22 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2607step0 permutation22 permutation18
    _ = injectiveMoment H node851 := by rfl

def raw2608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw2608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -1, -1, 0], ![1, 0, 1, -2]]

def raw2608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2608 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2608 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw2608 = injectiveMoment H raw2608step0 := by
      have heq : raw2608step0 = raw2608.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2608).symm
    injectiveMoment H raw2608step0 = injectiveMoment H raw2608step1 := by
      have heq : raw2608step1 = (fun i j => raw2608step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2608step0 permutation25 permutation18
    _ = injectiveMoment H node1078 := by rfl

def raw2609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -1, 0, -1], ![1, 0, 0, -1]]

def raw2609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2609 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2609 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw2609 = injectiveMoment H raw2609step0 := by
      have heq : raw2609step0 = raw2609.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2609).symm
    injectiveMoment H raw2609step0 = injectiveMoment H raw2609step1 := by
      have heq : raw2609step1 = (fun i j => raw2609step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2609step0 permutation25 permutation18
    _ = injectiveMoment H node1260 := by rfl

def raw2610 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 0, 0, 0], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2610step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![2, 0, 0, -2, 0], ![1, -1, 0, 1, -1]]

def raw2610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![1, -1, 1, -1]]

def raw2610step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2610 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2610 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw2610 = injectiveMoment H raw2610step0 := by
      have heq : raw2610step0 = raw2610.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2610).symm
    injectiveMoment H raw2610step0 = injectiveMoment H raw2610step1 := by
      have hz : ∀ i, raw2610step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2610step1 = (fun i j => raw2610step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2610step0 permutation80 hz
    injectiveMoment H raw2610step1 = injectiveMoment H raw2610step2 := by
      have heq : raw2610step2 = (fun i j => raw2610step1 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2610step1 permutation32 permutation30
    _ = injectiveMoment H node1110 := by rfl

def raw2611 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2611step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2611 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2611 = injectiveMoment H node1825 := by
  calc
    injectiveMoment H raw2611 = injectiveMoment H raw2611step0 := by
      have heq : raw2611step0 = (fun i j => raw2611 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2611 permutation33 permutation10
    _ = injectiveMoment H node1825 := by rfl

def raw2612 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw2612step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem canonical2612 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2612 = injectiveMoment H node1791 := by
  calc
    injectiveMoment H raw2612 = injectiveMoment H raw2612step0 := by
      have heq : raw2612step0 = (fun i j => raw2612 (permutation125 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2612 permutation125 permutation23
    _ = injectiveMoment H node1791 := by rfl

def raw2613 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2613step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2613 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2613 = injectiveMoment H node1823 := by
  calc
    injectiveMoment H raw2613 = injectiveMoment H raw2613step0 := by
      have heq : raw2613step0 = (fun i j => raw2613 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2613 permutation33 permutation10
    _ = injectiveMoment H node1823 := by rfl

def raw2614 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2614step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw2614step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical2614 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2614 = injectiveMoment H node1785 := by
  calc
    injectiveMoment H raw2614 = injectiveMoment H raw2614step0 := by
      have heq : raw2614step0 = -raw2614 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2614).symm
    injectiveMoment H raw2614step0 = injectiveMoment H raw2614step1 := by
      have heq : raw2614step1 = (fun i j => raw2614step0 (permutation45 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2614step0 permutation45 permutation26
    _ = injectiveMoment H node1785 := by rfl

def raw2615 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw2615step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 1, 0, 0]]

def raw2615step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical2615 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2615 = injectiveMoment H node1785 := by
  calc
    injectiveMoment H raw2615 = injectiveMoment H raw2615step0 := by
      have heq : raw2615step0 = -raw2615 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2615).symm
    injectiveMoment H raw2615step0 = injectiveMoment H raw2615step1 := by
      have heq : raw2615step1 = (fun i j => raw2615step0 (permutation51 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2615step0 permutation51 permutation26
    _ = injectiveMoment H node1785 := by rfl

def raw2616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw2616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![1, -1, -1, 1]]

def raw2616step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2616 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2616 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw2616 = injectiveMoment H raw2616step0 := by
      have heq : raw2616step0 = raw2616.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2616).symm
    injectiveMoment H raw2616step0 = injectiveMoment H raw2616step1 := by
      have heq : raw2616step1 = (fun i j => raw2616step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2616step0 permutation28 permutation17
    _ = injectiveMoment H node1107 := by rfl

def raw2617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 1, 0, -2]]

def raw2617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 0, -2, 0], ![1, -1, 2, -2]]

def raw2617step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2617 = injectiveMoment H node842 := by
  calc
    injectiveMoment H raw2617 = injectiveMoment H raw2617step0 := by
      have heq : raw2617step0 = raw2617.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2617).symm
    injectiveMoment H raw2617step0 = injectiveMoment H raw2617step1 := by
      have heq : raw2617step1 = (fun i j => raw2617step0 (permutation31 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2617step0 permutation31 permutation19
    _ = injectiveMoment H node842 := by rfl

def raw2618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw2618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 0, -1, -1], ![1, -1, 1, -1]]

def raw2618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical2618 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2618 = injectiveMoment H node1096 := by
  calc
    injectiveMoment H raw2618 = injectiveMoment H raw2618step0 := by
      have heq : raw2618step0 = raw2618.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2618).symm
    injectiveMoment H raw2618step0 = injectiveMoment H raw2618step1 := by
      have heq : raw2618step1 = (fun i j => raw2618step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2618step0 permutation31 permutation20
    _ = injectiveMoment H node1096 := by rfl

def raw2619 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2619step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 0, 0, -2], ![1, -1, 0, 0]]

def raw2619step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-2, 0, 0, 2], ![-1, 1, 0, 0]]

def raw2619step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical2619 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2619 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw2619 = injectiveMoment H raw2619step0 := by
      have heq : raw2619step0 = raw2619.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2619).symm
    injectiveMoment H raw2619step0 = injectiveMoment H raw2619step1 := by
      have heq : raw2619step1 = -raw2619step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2619step0).symm
    injectiveMoment H raw2619step1 = injectiveMoment H raw2619step2 := by
      have heq : raw2619step2 = (fun i j => raw2619step1 (permutation12 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2619step1 permutation12 permutation24
    _ = injectiveMoment H node1265 := by rfl

def raw2620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw2620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 0, 1, -3], ![1, -1, -1, 1]]

def raw2620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2620 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2620 = injectiveMoment H node1123 := by
  calc
    injectiveMoment H raw2620 = injectiveMoment H raw2620step0 := by
      have heq : raw2620step0 = raw2620.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2620).symm
    injectiveMoment H raw2620step0 = injectiveMoment H raw2620step1 := by
      have heq : raw2620step1 = (fun i j => raw2620step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2620step0 permutation31 permutation18
    _ = injectiveMoment H node1123 := by rfl

def raw2621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw2621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical2621 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2621 = injectiveMoment H node513 := by
  calc
    injectiveMoment H raw2621 = injectiveMoment H raw2621step0 := by
      have heq : raw2621step0 = (fun i j => raw2621 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2621 permutation9 permutation10
    _ = injectiveMoment H node513 := by rfl

def raw2622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw2622step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 1, 0, -3], ![1, -2, 0, 1]]

def raw2622step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-2, -1, 0, 3], ![-1, 2, 0, -1]]

def raw2622step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical2622 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2622 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw2622 = injectiveMoment H raw2622step0 := by
      have heq : raw2622step0 = raw2622.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2622).symm
    injectiveMoment H raw2622step0 = injectiveMoment H raw2622step1 := by
      have heq : raw2622step1 = -raw2622step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2622step0).symm
    injectiveMoment H raw2622step1 = injectiveMoment H raw2622step2 := by
      have heq : raw2622step2 = (fun i j => raw2622step1 (permutation12 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2622step1 permutation12 permutation24
    _ = injectiveMoment H node1249 := by rfl

def raw2623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2623step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -3, 0, 1], ![1, 1, 0, -2]]

def raw2623step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 3, 0, -1], ![-1, -1, 0, 2]]

def raw2623step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2623 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2623 = injectiveMoment H node1016 := by
  calc
    injectiveMoment H raw2623 = injectiveMoment H raw2623step0 := by
      have heq : raw2623step0 = raw2623.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2623).symm
    injectiveMoment H raw2623step0 = injectiveMoment H raw2623step1 := by
      have heq : raw2623step1 = -raw2623step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2623step0).symm
    injectiveMoment H raw2623step1 = injectiveMoment H raw2623step2 := by
      have heq : raw2623step2 = (fun i j => raw2623step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2623step1 permutation12 permutation26
    _ = injectiveMoment H node1016 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
