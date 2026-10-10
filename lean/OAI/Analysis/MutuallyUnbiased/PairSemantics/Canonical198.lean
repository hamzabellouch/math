import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6336 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, -1, 3, -3], ![0, 2, -2, 0]]

def raw6336step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 3, -2], ![3, -3, 0]]

def raw6336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical6336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6336 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw6336 = injectiveMoment H raw6336step0 := by
      have heq : raw6336step0 = raw6336.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6336).symm
    injectiveMoment H raw6336step0 = injectiveMoment H raw6336step1 := by
      have heq : raw6336step1 = (fun i j => raw6336step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6336step0 permutation22 permutation7
    _ = injectiveMoment H node170 := by rfl

def raw6337 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, 0, -2, 1], ![0, 1, 3, -4]]

def raw6337step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![3, 1, -4]]

def raw6337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6337 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6337 = injectiveMoment H raw6337step0 := by
      have heq : raw6337step0 = raw6337.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6337).symm
    injectiveMoment H raw6337step0 = injectiveMoment H raw6337step1 := by
      have heq : raw6337step1 = (fun i j => raw6337step0 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6337step0 permutation23 permutation5
    _ = injectiveMoment H node173 := by rfl

def raw6338 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, 0, 3, -4], ![0, 1, -2, 1]]

def raw6338step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 3, -2], ![3, -4, 1]]

def raw6338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6338 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6338 = injectiveMoment H raw6338step0 := by
      have heq : raw6338step0 = raw6338.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6338).symm
    injectiveMoment H raw6338step0 = injectiveMoment H raw6338step1 := by
      have heq : raw6338step1 = (fun i j => raw6338step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6338step0 permutation21 permutation7
    _ = injectiveMoment H node173 := by rfl

def raw6339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6339step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical6339 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6339 = injectiveMoment H node2856 := by
  calc
    injectiveMoment H raw6339 = injectiveMoment H raw6339step0 := by
      have heq : raw6339step0 = (fun i j => raw6339 (permutation131 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6339 permutation131 permutation21
    _ = injectiveMoment H node2856 := by rfl

def raw6340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw6340step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw6340step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical6340 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6340 = injectiveMoment H node1560 := by
  calc
    injectiveMoment H raw6340 = injectiveMoment H raw6340step0 := by
      have heq : raw6340step0 = -raw6340 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6340).symm
    injectiveMoment H raw6340step0 = injectiveMoment H raw6340step1 := by
      have heq : raw6340step1 = (fun i j => raw6340step0 (permutation146 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6340step0 permutation146 permutation21
    _ = injectiveMoment H node1560 := by rfl

def raw6341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw6341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical6341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6341 = injectiveMoment H node2577 := by
  calc
    injectiveMoment H raw6341 = injectiveMoment H raw6341step0 := by
      have heq : raw6341step0 = (fun i j => raw6341 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6341 permutation36 permutation15
    _ = injectiveMoment H node2577 := by rfl

def raw6342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical6342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6342 = injectiveMoment H node2561 := by
  rfl

def raw6343 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw6343step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical6343 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6343 = injectiveMoment H node2575 := by
  calc
    injectiveMoment H raw6343 = injectiveMoment H raw6343step0 := by
      have heq : raw6343step0 = (fun i j => raw6343 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6343 permutation36 permutation15
    _ = injectiveMoment H node2575 := by rfl

def raw6344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw6344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem canonical6344 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6344 = injectiveMoment H node997 := by
  calc
    injectiveMoment H raw6344 = injectiveMoment H raw6344step0 := by
      have heq : raw6344step0 = (fun i j => raw6344 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6344 permutation10 permutation15
    _ = injectiveMoment H node997 := by rfl

def raw6345 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw6345step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, 0, 1, -2], ![0, -2, 2, 0], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw6345step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical6345 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6345 = injectiveMoment H node2143 := by
  calc
    injectiveMoment H raw6345 = injectiveMoment H raw6345step0 := by
      have heq : raw6345step0 = -raw6345 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6345).symm
    injectiveMoment H raw6345step0 = injectiveMoment H raw6345step1 := by
      have heq : raw6345step1 = (fun i j => raw6345step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6345step0 permutation101 permutation15
    _ = injectiveMoment H node2143 := by rfl

def raw6346 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6346step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, 0, 1, -2], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6346step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical6346 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6346 = injectiveMoment H node1487 := by
  calc
    injectiveMoment H raw6346 = injectiveMoment H raw6346step0 := by
      have heq : raw6346step0 = -raw6346 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6346).symm
    injectiveMoment H raw6346step0 = injectiveMoment H raw6346step1 := by
      have heq : raw6346step1 = (fun i j => raw6346step0 (permutation101 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6346step0 permutation101 permutation17
    _ = injectiveMoment H node1487 := by rfl

def raw6347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def raw6347step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical6347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6347 = injectiveMoment H node996 := by
  calc
    injectiveMoment H raw6347 = injectiveMoment H raw6347step0 := by
      have heq : raw6347step0 = (fun i j => raw6347 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6347 permutation9 permutation15
    _ = injectiveMoment H node996 := by rfl

def raw6348 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical6348 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6348 = injectiveMoment H node2564 := by
  rfl

def raw6349 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

theorem canonical6349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6349 = injectiveMoment H node2565 := by
  rfl

def raw6350 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical6350 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6350 = injectiveMoment H node2566 := by
  rfl

def raw6351 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical6351 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6351 = injectiveMoment H node2567 := by
  rfl

def raw6352 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw6352step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 1, -1], ![0, -2, 3, -1], ![2, 2, -4, 0]]

def raw6352step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, -1, 1], ![0, 2, -3, 1], ![-2, -2, 4, 0]]

def raw6352step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical6352 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6352 = injectiveMoment H node583 := by
  calc
    injectiveMoment H raw6352 = injectiveMoment H raw6352step0 := by
      have heq : raw6352step0 = raw6352.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6352).symm
    injectiveMoment H raw6352step0 = injectiveMoment H raw6352step1 := by
      have heq : raw6352step1 = -raw6352step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6352step0).symm
    injectiveMoment H raw6352step1 = injectiveMoment H raw6352step2 := by
      have heq : raw6352step2 = (fun i j => raw6352step1 (permutation31 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6352step1 permutation31 permutation13
    _ = injectiveMoment H node583 := by rfl

def raw6353 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw6353step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, -2, 0, 2], ![2, 2, 0, -4]]

def raw6353step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical6353 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6353 = injectiveMoment H node1113 := by
  calc
    injectiveMoment H raw6353 = injectiveMoment H raw6353step0 := by
      have heq : raw6353step0 = raw6353.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6353).symm
    injectiveMoment H raw6353step0 = injectiveMoment H raw6353step1 := by
      have heq : raw6353step1 = (fun i j => raw6353step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6353step0 permutation18 permutation21
    _ = injectiveMoment H node1113 := by rfl

def raw6354 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 1, -1, -1]]

def raw6354step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, -2, 3, -1], ![2, 2, -3, -1]]

def raw6354step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![0, 2, -3, 1], ![-2, -2, 3, 1]]

def raw6354step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical6354 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6354 = injectiveMoment H node677 := by
  calc
    injectiveMoment H raw6354 = injectiveMoment H raw6354step0 := by
      have heq : raw6354step0 = raw6354.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6354).symm
    injectiveMoment H raw6354step0 = injectiveMoment H raw6354step1 := by
      have heq : raw6354step1 = -raw6354step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6354step0).symm
    injectiveMoment H raw6354step1 = injectiveMoment H raw6354step2 := by
      have heq : raw6354step2 = (fun i j => raw6354step1 (permutation32 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6354step1 permutation32 permutation13
    _ = injectiveMoment H node677 := by rfl

def raw6355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw6355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

theorem canonical6355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6355 = injectiveMoment H node1082 := by
  calc
    injectiveMoment H raw6355 = injectiveMoment H raw6355step0 := by
      have heq : raw6355step0 = (fun i j => raw6355 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6355 permutation12 permutation15
    _ = injectiveMoment H node1082 := by rfl

def raw6356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw6356step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical6356 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6356 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw6356 = injectiveMoment H raw6356step0 := by
      have heq : raw6356step0 = (fun i j => raw6356 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6356 permutation14 permutation15
    _ = injectiveMoment H node1083 := by rfl

def raw6357 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw6357step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

theorem canonical6357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6357 = injectiveMoment H node1082 := by
  calc
    injectiveMoment H raw6357 = injectiveMoment H raw6357step0 := by
      have heq : raw6357step0 = (fun i j => raw6357 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6357 permutation14 permutation15
    _ = injectiveMoment H node1082 := by rfl

def raw6358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical6358 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6358 = injectiveMoment H node2568 := by
  rfl

def raw6359 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

theorem canonical6359 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6359 = injectiveMoment H node2569 := by
  rfl

def raw6360 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![2, -1, 3, -4]]

def raw6360step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![2, 1, 1, -4]]

def raw6360step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, -1, 1], ![0, 1, 2, -3], ![-2, -1, -1, 4]]

def raw6360step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical6360 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6360 = injectiveMoment H node466 := by
  calc
    injectiveMoment H raw6360 = injectiveMoment H raw6360step0 := by
      have heq : raw6360step0 = raw6360.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6360).symm
    injectiveMoment H raw6360step0 = injectiveMoment H raw6360step1 := by
      have heq : raw6360step1 = -raw6360step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6360step0).symm
    injectiveMoment H raw6360step1 = injectiveMoment H raw6360step2 := by
      have heq : raw6360step2 = (fun i j => raw6360step1 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6360step1 permutation32 permutation9
    _ = injectiveMoment H node466 := by rfl

def raw6361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem canonical6361 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6361 = injectiveMoment H node2570 := by
  rfl

def raw6362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw6362step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw6362step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical6362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6362 = injectiveMoment H node1640 := by
  calc
    injectiveMoment H raw6362 = injectiveMoment H raw6362step0 := by
      have heq : raw6362step0 = -raw6362 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6362).symm
    injectiveMoment H raw6362step0 = injectiveMoment H raw6362step1 := by
      have heq : raw6362step1 = (fun i j => raw6362step0 (permutation146 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6362step0 permutation146 permutation21
    _ = injectiveMoment H node1640 := by rfl

def raw6363 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw6363step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw6363step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical6363 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6363 = injectiveMoment H node1740 := by
  calc
    injectiveMoment H raw6363 = injectiveMoment H raw6363step0 := by
      have heq : raw6363step0 = -raw6363 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6363).symm
    injectiveMoment H raw6363step0 = injectiveMoment H raw6363step1 := by
      have heq : raw6363step1 = (fun i j => raw6363step0 (permutation123 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6363step0 permutation123 permutation21
    _ = injectiveMoment H node1740 := by rfl

def raw6364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical6364 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6364 = injectiveMoment H node2571 := by
  rfl

def raw6365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw6365step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical6365 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6365 = injectiveMoment H node1772 := by
  calc
    injectiveMoment H raw6365 = injectiveMoment H raw6365step0 := by
      have heq : raw6365step0 = -raw6365 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6365).symm
    injectiveMoment H raw6365step0 = injectiveMoment H raw6365step1 := by
      have heq : raw6365step1 = (fun i j => raw6365step0 (permutation117 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6365step0 permutation117 permutation21
    _ = injectiveMoment H node1772 := by rfl

def raw6366 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

theorem canonical6366 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6366 = injectiveMoment H node2572 := by
  rfl

def raw6367 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6367step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6367step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical6367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6367 = injectiveMoment H node1719 := by
  calc
    injectiveMoment H raw6367 = injectiveMoment H raw6367step0 := by
      have heq : raw6367step0 = -raw6367 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6367).symm
    injectiveMoment H raw6367step0 = injectiveMoment H raw6367step1 := by
      have heq : raw6367step1 = (fun i j => raw6367step0 (permutation92 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6367step0 permutation92 permutation23
    _ = injectiveMoment H node1719 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
