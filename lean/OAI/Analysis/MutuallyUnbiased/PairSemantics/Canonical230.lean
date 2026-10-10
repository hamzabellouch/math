import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw7360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw7360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7360 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7360 = injectiveMoment H node1391 := by
  calc
    injectiveMoment H raw7360 = injectiveMoment H raw7360step0 := by
      have heq : raw7360step0 = -raw7360 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7360).symm
    injectiveMoment H raw7360step0 = injectiveMoment H raw7360step1 := by
      have heq : raw7360step1 = (fun i j => raw7360step0 (permutation311 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7360step0 permutation311 permutation5
    _ = injectiveMoment H node1391 := by rfl

def raw7361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw7361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw7361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical7361 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7361 = injectiveMoment H node1530 := by
  calc
    injectiveMoment H raw7361 = injectiveMoment H raw7361step0 := by
      have heq : raw7361step0 = -raw7361 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7361).symm
    injectiveMoment H raw7361step0 = injectiveMoment H raw7361step1 := by
      have heq : raw7361step1 = (fun i j => raw7361step0 (permutation404 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7361step0 permutation404 permutation3
    _ = injectiveMoment H node1530 := by rfl

def raw7362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw7362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-2, -1, 3]]

def raw7362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical7362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7362 = injectiveMoment H node1860 := by
  calc
    injectiveMoment H raw7362 = injectiveMoment H raw7362step0 := by
      have heq : raw7362step0 = -raw7362 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7362).symm
    injectiveMoment H raw7362step0 = injectiveMoment H raw7362step1 := by
      have heq : raw7362step1 = (fun i j => raw7362step0 (permutation387 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7362step0 permutation387 permutation3
    _ = injectiveMoment H node1860 := by rfl

def raw7363 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw7363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical7363 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7363 = injectiveMoment H node734 := by
  calc
    injectiveMoment H raw7363 = injectiveMoment H raw7363step0 := by
      have heq : raw7363step0 = (fun i j => raw7363 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7363 permutation57 permutation3
    _ = injectiveMoment H node734 := by rfl

def raw7364 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7364 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7364 = injectiveMoment H node864 := by
  calc
    injectiveMoment H raw7364 = injectiveMoment H raw7364step0 := by
      have heq : raw7364step0 = (fun i j => raw7364 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7364 permutation57 permutation3
    _ = injectiveMoment H node864 := by rfl

def raw7365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw7365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical7365 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7365 = injectiveMoment H node865 := by
  calc
    injectiveMoment H raw7365 = injectiveMoment H raw7365step0 := by
      have heq : raw7365step0 = (fun i j => raw7365 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7365 permutation57 permutation3
    _ = injectiveMoment H node865 := by rfl

def raw7366 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 3, -4]]

def raw7366step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, -3, 4]]

def raw7366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7366 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7366 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw7366 = injectiveMoment H raw7366step0 := by
      have heq : raw7366step0 = -raw7366 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7366).symm
    injectiveMoment H raw7366step0 = injectiveMoment H raw7366step1 := by
      have heq : raw7366step1 = (fun i j => raw7366step0 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7366step0 permutation31 permutation3
    _ = injectiveMoment H node243 := by rfl

def raw7367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw7367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -4, 5]]

def raw7367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7367 = injectiveMoment H node2375 := by
  calc
    injectiveMoment H raw7367 = injectiveMoment H raw7367step0 := by
      have heq : raw7367step0 = -raw7367 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7367).symm
    injectiveMoment H raw7367step0 = injectiveMoment H raw7367step1 := by
      have heq : raw7367step1 = (fun i j => raw7367step0 (permutation404 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7367step0 permutation404 permutation3
    _ = injectiveMoment H node2375 := by rfl

def raw7368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw7368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7368 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7368 = injectiveMoment H node2466 := by
  calc
    injectiveMoment H raw7368 = injectiveMoment H raw7368step0 := by
      have heq : raw7368step0 = -raw7368 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7368).symm
    injectiveMoment H raw7368step0 = injectiveMoment H raw7368step1 := by
      have heq : raw7368step1 = (fun i j => raw7368step0 (permutation408 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7368step0 permutation408 permutation3
    _ = injectiveMoment H node2466 := by rfl

def raw7369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def raw7369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical7369 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7369 = injectiveMoment H node2658 := by
  calc
    injectiveMoment H raw7369 = injectiveMoment H raw7369step0 := by
      have heq : raw7369step0 = (fun i j => raw7369 (permutation203 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7369 permutation203 permutation3
    _ = injectiveMoment H node2658 := by rfl

def raw7370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw7370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7370 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7370 = injectiveMoment H node2657 := by
  calc
    injectiveMoment H raw7370 = injectiveMoment H raw7370step0 := by
      have heq : raw7370step0 = (fun i j => raw7370 (permutation203 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7370 permutation203 permutation3
    _ = injectiveMoment H node2657 := by rfl

def raw7371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7371 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7371 = injectiveMoment H node2660 := by
  calc
    injectiveMoment H raw7371 = injectiveMoment H raw7371step0 := by
      have heq : raw7371step0 = (fun i j => raw7371 (permutation202 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7371 permutation202 permutation3
    _ = injectiveMoment H node2660 := by rfl

def raw7372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7372 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7372 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw7372 = injectiveMoment H raw7372step0 := by
      have heq : raw7372step0 = (fun i j => raw7372 (permutation60 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7372 permutation60 permutation5
    _ = injectiveMoment H node1151 := by rfl

def raw7373 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]

def raw7373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7373 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7373 = injectiveMoment H node659 := by
  calc
    injectiveMoment H raw7373 = injectiveMoment H raw7373step0 := by
      have heq : raw7373step0 = -raw7373 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7373).symm
    injectiveMoment H raw7373step0 = injectiveMoment H raw7373step1 := by
      have heq : raw7373step1 = (fun i j => raw7373step0 (permutation99 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7373step0 permutation99 permutation5
    _ = injectiveMoment H node659 := by rfl

def raw7374 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw7374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical7374 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7374 = injectiveMoment H node1138 := by
  calc
    injectiveMoment H raw7374 = injectiveMoment H raw7374step0 := by
      have heq : raw7374step0 = (fun i j => raw7374 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7374 permutation57 permutation3
    _ = injectiveMoment H node1138 := by rfl

def raw7375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical7375 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7375 = injectiveMoment H node1139 := by
  calc
    injectiveMoment H raw7375 = injectiveMoment H raw7375step0 := by
      have heq : raw7375step0 = (fun i j => raw7375 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7375 permutation57 permutation3
    _ = injectiveMoment H node1139 := by rfl

def raw7376 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 3, -4]]

def raw7376step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, -3, 4]]

def raw7376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7376 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7376 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw7376 = injectiveMoment H raw7376step0 := by
      have heq : raw7376step0 = -raw7376 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7376).symm
    injectiveMoment H raw7376step0 = injectiveMoment H raw7376step1 := by
      have heq : raw7376step1 = (fun i j => raw7376step0 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7376step0 permutation31 permutation3
    _ = injectiveMoment H node246 := by rfl

def raw7377 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2]]

def raw7377step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical7377 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7377 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw7377 = injectiveMoment H raw7377step0 := by
      have heq : raw7377step0 = (fun i j => raw7377 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7377 permutation15 permutation5
    _ = injectiveMoment H node283 := by rfl

def raw7378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def raw7378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -3, 5]]

def raw7378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7378 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7378 = injectiveMoment H node1381 := by
  calc
    injectiveMoment H raw7378 = injectiveMoment H raw7378step0 := by
      have heq : raw7378step0 = -raw7378 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7378).symm
    injectiveMoment H raw7378step0 = injectiveMoment H raw7378step1 := by
      have heq : raw7378step1 = (fun i j => raw7378step0 (permutation313 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7378step0 permutation313 permutation5
    _ = injectiveMoment H node1381 := by rfl

def raw7379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw7379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw7379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7379 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7379 = injectiveMoment H node1390 := by
  calc
    injectiveMoment H raw7379 = injectiveMoment H raw7379step0 := by
      have heq : raw7379step0 = -raw7379 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7379).symm
    injectiveMoment H raw7379step0 = injectiveMoment H raw7379step1 := by
      have heq : raw7379step1 = (fun i j => raw7379step0 (permutation311 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7379step0 permutation311 permutation5
    _ = injectiveMoment H node1390 := by rfl

def raw7380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]

def raw7380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![-2, -3, 5]]

def raw7380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7380 = injectiveMoment H node1381 := by
  calc
    injectiveMoment H raw7380 = injectiveMoment H raw7380step0 := by
      have heq : raw7380step0 = -raw7380 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7380).symm
    injectiveMoment H raw7380step0 = injectiveMoment H raw7380step1 := by
      have heq : raw7380step1 = (fun i j => raw7380step0 (permutation312 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7380step0 permutation312 permutation5
    _ = injectiveMoment H node1381 := by rfl

def raw7381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw7381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw7381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical7381 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7381 = injectiveMoment H node1438 := by
  calc
    injectiveMoment H raw7381 = injectiveMoment H raw7381step0 := by
      have heq : raw7381step0 = -raw7381 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7381).symm
    injectiveMoment H raw7381step0 = injectiveMoment H raw7381step1 := by
      have heq : raw7381step1 = (fun i j => raw7381step0 (permutation366 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7381step0 permutation366 permutation3
    _ = injectiveMoment H node1438 := by rfl

def raw7382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw7382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -3, 4]]

def raw7382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical7382 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7382 = injectiveMoment H node2380 := by
  calc
    injectiveMoment H raw7382 = injectiveMoment H raw7382step0 := by
      have heq : raw7382step0 = -raw7382 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7382).symm
    injectiveMoment H raw7382step0 = injectiveMoment H raw7382step1 := by
      have heq : raw7382step1 = (fun i j => raw7382step0 (permutation404 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7382step0 permutation404 permutation3
    _ = injectiveMoment H node2380 := by rfl

def raw7383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 3, -4]]

def raw7383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, -3, 4]]

def raw7383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical7383 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7383 = injectiveMoment H node2380 := by
  calc
    injectiveMoment H raw7383 = injectiveMoment H raw7383step0 := by
      have heq : raw7383step0 = -raw7383 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7383).symm
    injectiveMoment H raw7383step0 = injectiveMoment H raw7383step1 := by
      have heq : raw7383step1 = (fun i j => raw7383step0 (permutation387 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7383step0 permutation387 permutation3
    _ = injectiveMoment H node2380 := by rfl

def raw7384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 3, -3]]

def raw7384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical7384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7384 = injectiveMoment H node2791 := by
  calc
    injectiveMoment H raw7384 = injectiveMoment H raw7384step0 := by
      have heq : raw7384step0 = (fun i j => raw7384 (permutation155 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7384 permutation155 permutation3
    _ = injectiveMoment H node2791 := by rfl

def raw7385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

theorem canonical7385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7385 = injectiveMoment H node2792 := by
  rfl

def raw7386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7386 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7386 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7386 = injectiveMoment H raw7386step0 := by
      have heq : raw7386step0 = (fun i j => raw7386 (permutation122 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7386 permutation122 permutation6
    _ = injectiveMoment H node1294 := by rfl

def raw7387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw7387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw7387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7387 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7387 = injectiveMoment H node1531 := by
  calc
    injectiveMoment H raw7387 = injectiveMoment H raw7387step0 := by
      have heq : raw7387step0 = -raw7387 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7387).symm
    injectiveMoment H raw7387step0 = injectiveMoment H raw7387step1 := by
      have heq : raw7387step1 = (fun i j => raw7387step0 (permutation407 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7387step0 permutation407 permutation3
    _ = injectiveMoment H node1531 := by rfl

def raw7388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw7388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

theorem canonical7388 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7388 = injectiveMoment H node1428 := by
  calc
    injectiveMoment H raw7388 = injectiveMoment H raw7388step0 := by
      have heq : raw7388step0 = (fun i j => raw7388 (permutation379 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7388 permutation379 permutation8
    _ = injectiveMoment H node1428 := by rfl

def raw7389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]

def raw7389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![-2, -2, 4]]

def raw7389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7389 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7389 = injectiveMoment H node1531 := by
  calc
    injectiveMoment H raw7389 = injectiveMoment H raw7389step0 := by
      have heq : raw7389step0 = -raw7389 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7389).symm
    injectiveMoment H raw7389step0 = injectiveMoment H raw7389step1 := by
      have heq : raw7389step1 = (fun i j => raw7389step0 (permutation403 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7389step0 permutation403 permutation3
    _ = injectiveMoment H node1531 := by rfl

def raw7390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]

def raw7390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -2, 4]]

def raw7390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7390 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7390 = injectiveMoment H node1542 := by
  calc
    injectiveMoment H raw7390 = injectiveMoment H raw7390step0 := by
      have heq : raw7390step0 = -raw7390 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7390).symm
    injectiveMoment H raw7390step0 = injectiveMoment H raw7390step1 := by
      have heq : raw7390step1 = (fun i j => raw7390step0 (permutation367 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7390step0 permutation367 permutation3
    _ = injectiveMoment H node1542 := by rfl

def raw7391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw7391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3]]

def raw7391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7391 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7391 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw7391 = injectiveMoment H raw7391step0 := by
      have heq : raw7391step0 = -raw7391 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7391).symm
    injectiveMoment H raw7391step0 = injectiveMoment H raw7391step1 := by
      have heq : raw7391step1 = (fun i j => raw7391step0 (permutation405 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7391step0 permutation405 permutation3
    _ = injectiveMoment H node2469 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
