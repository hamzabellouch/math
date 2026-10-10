import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6432 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw6432step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical6432 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6432 = injectiveMoment H node1031 := by
  calc
    injectiveMoment H raw6432 = injectiveMoment H raw6432step0 := by
      have heq : raw6432step0 = (fun i j => raw6432 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6432 permutation10 permutation15
    _ = injectiveMoment H node1031 := by rfl

def raw6433 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem canonical6433 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6433 = injectiveMoment H node1035 := by
  rfl

def raw6434 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw6434step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-1, 1, -2, 2]]

def raw6434step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical6434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6434 = injectiveMoment H node831 := by
  calc
    injectiveMoment H raw6434 = injectiveMoment H raw6434step0 := by
      have heq : raw6434step0 = -raw6434 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6434).symm
    injectiveMoment H raw6434step0 = injectiveMoment H raw6434step1 := by
      have heq : raw6434step1 = (fun i j => raw6434step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6434step0 permutation32 permutation11
    _ = injectiveMoment H node831 := by rfl

def raw6435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical6435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6435 = injectiveMoment H node1036 := by
  rfl

def raw6436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical6436 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6436 = injectiveMoment H node1037 := by
  rfl

def raw6437 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw6437step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 2, -4]]

def raw6437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 2, -2], ![-2, -2, 4]]

def raw6437step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical6437 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6437 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw6437 = injectiveMoment H raw6437step0 := by
      have heq : raw6437step0 = raw6437.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6437).symm
    injectiveMoment H raw6437step0 = injectiveMoment H raw6437step1 := by
      have heq : raw6437step1 = -raw6437step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6437step0).symm
    injectiveMoment H raw6437step1 = injectiveMoment H raw6437step2 := by
      have heq : raw6437step2 = (fun i j => raw6437step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6437step1 permutation27 permutation5
    _ = injectiveMoment H node145 := by rfl

def raw6438 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![-1, 2, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6438step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![1, -2, 2, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw6438step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

theorem canonical6438 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6438 = injectiveMoment H node2323 := by
  calc
    injectiveMoment H raw6438 = injectiveMoment H raw6438step0 := by
      have heq : raw6438step0 = -raw6438 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6438).symm
    injectiveMoment H raw6438step0 = injectiveMoment H raw6438step1 := by
      have heq : raw6438step1 = (fun i j => raw6438step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6438step0 permutation101 permutation15
    _ = injectiveMoment H node2323 := by rfl

def raw6439 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6439step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![1, -2, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw6439step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

theorem canonical6439 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6439 = injectiveMoment H node2254 := by
  calc
    injectiveMoment H raw6439 = injectiveMoment H raw6439step0 := by
      have heq : raw6439step0 = -raw6439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6439).symm
    injectiveMoment H raw6439step0 = injectiveMoment H raw6439step1 := by
      have heq : raw6439step1 = (fun i j => raw6439step0 (permutation101 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6439step0 permutation101 permutation16
    _ = injectiveMoment H node2254 := by rfl

def raw6440 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw6440step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![1, -2, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 2, -1]]

def raw6440step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

theorem canonical6440 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6440 = injectiveMoment H node2260 := by
  calc
    injectiveMoment H raw6440 = injectiveMoment H raw6440step0 := by
      have heq : raw6440step0 = -raw6440 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6440).symm
    injectiveMoment H raw6440step0 = injectiveMoment H raw6440step1 := by
      have heq : raw6440step1 = (fun i j => raw6440step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6440step0 permutation101 permutation15
    _ = injectiveMoment H node2260 := by rfl

def raw6441 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6441step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![-1, 0, 0, 1]]

def raw6441step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical6441 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6441 = injectiveMoment H node2700 := by
  calc
    injectiveMoment H raw6441 = injectiveMoment H raw6441step0 := by
      have heq : raw6441step0 = -raw6441 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6441).symm
    injectiveMoment H raw6441step0 = injectiveMoment H raw6441step1 := by
      have heq : raw6441step1 = (fun i j => raw6441step0 (permutation126 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6441step0 permutation126 permutation21
    _ = injectiveMoment H node2700 := by rfl

def raw6442 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw6442step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw6442step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical6442 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6442 = injectiveMoment H node2907 := by
  calc
    injectiveMoment H raw6442 = injectiveMoment H raw6442step0 := by
      have heq : raw6442step0 = -raw6442 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6442).symm
    injectiveMoment H raw6442step0 = injectiveMoment H raw6442step1 := by
      have heq : raw6442step1 = (fun i j => raw6442step0 (permutation380 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6442step0 permutation380 permutation9
    _ = injectiveMoment H node2907 := by rfl

def raw6443 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical6443 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6443 = injectiveMoment H node2593 := by
  rfl

def raw6444 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw6444step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical6444 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6444 = injectiveMoment H node2594 := by
  calc
    injectiveMoment H raw6444 = injectiveMoment H raw6444step0 := by
      have heq : raw6444step0 = (fun i j => raw6444 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6444 permutation34 permutation15
    _ = injectiveMoment H node2594 := by rfl

def raw6445 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw6445step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical6445 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6445 = injectiveMoment H node2593 := by
  calc
    injectiveMoment H raw6445 = injectiveMoment H raw6445step0 := by
      have heq : raw6445step0 = (fun i j => raw6445 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6445 permutation34 permutation15
    _ = injectiveMoment H node2593 := by rfl

def raw6446 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical6446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6446 = injectiveMoment H node2595 := by
  rfl

def raw6447 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical6447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6447 = injectiveMoment H node2596 := by
  rfl

def raw6448 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw6448step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw6448step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical6448 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6448 = injectiveMoment H node3297 := by
  calc
    injectiveMoment H raw6448 = injectiveMoment H raw6448step0 := by
      have heq : raw6448step0 = -raw6448 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6448).symm
    injectiveMoment H raw6448step0 = injectiveMoment H raw6448step1 := by
      have heq : raw6448step1 = (fun i j => raw6448step0 (permutation300 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6448step0 permutation300 permutation15
    _ = injectiveMoment H node3297 := by rfl

def raw6449 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical6449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6449 = injectiveMoment H node2601 := by
  rfl

def raw6450 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw6450step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical6450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6450 = injectiveMoment H node2599 := by
  calc
    injectiveMoment H raw6450 = injectiveMoment H raw6450step0 := by
      have heq : raw6450step0 = (fun i j => raw6450 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6450 permutation35 permutation9
    _ = injectiveMoment H node2599 := by rfl

def raw6451 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical6451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6451 = injectiveMoment H node2603 := by
  rfl

def raw6452 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![0, 1, 0, -1]]

def raw6452step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6452 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6452 = injectiveMoment H node2602 := by
  calc
    injectiveMoment H raw6452 = injectiveMoment H raw6452step0 := by
      have heq : raw6452step0 = (fun i j => raw6452 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6452 permutation34 permutation9
    _ = injectiveMoment H node2602 := by rfl

def raw6453 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical6453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6453 = injectiveMoment H node1042 := by
  rfl

def raw6454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, 3, -4]]

def raw6454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical6454 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6454 = injectiveMoment H node2593 := by
  calc
    injectiveMoment H raw6454 = injectiveMoment H raw6454step0 := by
      have heq : raw6454step0 = (fun i j => raw6454 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6454 permutation35 permutation9
    _ = injectiveMoment H node2593 := by rfl

def raw6455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw6455step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6455 = injectiveMoment H node2598 := by
  calc
    injectiveMoment H raw6455 = injectiveMoment H raw6455step0 := by
      have heq : raw6455step0 = (fun i j => raw6455 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6455 permutation35 permutation9
    _ = injectiveMoment H node2598 := by rfl

def raw6456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw6456step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical6456 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6456 = injectiveMoment H node2600 := by
  calc
    injectiveMoment H raw6456 = injectiveMoment H raw6456step0 := by
      have heq : raw6456step0 = (fun i j => raw6456 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6456 permutation35 permutation9
    _ = injectiveMoment H node2600 := by rfl

def raw6457 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw6457step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw6457step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical6457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6457 = injectiveMoment H node3103 := by
  calc
    injectiveMoment H raw6457 = injectiveMoment H raw6457step0 := by
      have heq : raw6457step0 = -raw6457 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6457).symm
    injectiveMoment H raw6457step0 = injectiveMoment H raw6457step1 := by
      have heq : raw6457step1 = (fun i j => raw6457step0 (permutation365 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6457step0 permutation365 permutation9
    _ = injectiveMoment H node3103 := by rfl

def raw6458 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3]]

theorem canonical6458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6458 = injectiveMoment H node2604 := by
  rfl

def raw6459 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical6459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6459 = injectiveMoment H node2605 := by
  rfl

def raw6460 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6460 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6460 = injectiveMoment H node2606 := by
  rfl

def raw6461 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![0, 1, -1, 0]]

def raw6461step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3]]

theorem canonical6461 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6461 = injectiveMoment H node2604 := by
  calc
    injectiveMoment H raw6461 = injectiveMoment H raw6461step0 := by
      have heq : raw6461step0 = (fun i j => raw6461 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6461 permutation34 permutation9
    _ = injectiveMoment H node2604 := by rfl

def raw6462 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6462 = injectiveMoment H node1043 := by
  rfl

def raw6463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 0, 3, -3], ![1, 0, -2, 1]]

def raw6463step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical6463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6463 = injectiveMoment H node2599 := by
  calc
    injectiveMoment H raw6463 = injectiveMoment H raw6463step0 := by
      have heq : raw6463step0 = (fun i j => raw6463 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6463 permutation36 permutation15
    _ = injectiveMoment H node2599 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
