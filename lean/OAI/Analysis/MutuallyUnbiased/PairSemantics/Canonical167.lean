import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5344 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5344step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical5344 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5344 = injectiveMoment H node1748 := by
  calc
    injectiveMoment H raw5344 = injectiveMoment H raw5344step0 := by
      have heq : raw5344step0 = (fun i j => raw5344 (permutation33 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5344 permutation33 permutation12
    _ = injectiveMoment H node1748 := by rfl

def raw5345 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 1, 1], ![1, 1, -1, -1]]

def raw5345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem canonical5345 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5345 = injectiveMoment H node1344 := by
  calc
    injectiveMoment H raw5345 = injectiveMoment H raw5345step0 := by
      have heq : raw5345step0 = raw5345.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5345).symm
    injectiveMoment H raw5345step0 = injectiveMoment H raw5345step1 := by
      have heq : raw5345step1 = (fun i j => raw5345step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5345step0 permutation21 permutation17
    _ = injectiveMoment H node1344 := by rfl

def raw5346 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5346step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical5346 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5346 = injectiveMoment H node1752 := by
  calc
    injectiveMoment H raw5346 = injectiveMoment H raw5346step0 := by
      have heq : raw5346step0 = (fun i j => raw5346 (permutation33 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5346 permutation33 permutation12
    _ = injectiveMoment H node1752 := by rfl

def raw5347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5347step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 2, 0], ![1, 1, -2, 0]]

def raw5347step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5347 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw5347 = injectiveMoment H raw5347step0 := by
      have heq : raw5347step0 = raw5347.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5347).symm
    injectiveMoment H raw5347step0 = injectiveMoment H raw5347step1 := by
      have heq : raw5347step1 = (fun i j => raw5347step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5347step0 permutation23 permutation20
    _ = injectiveMoment H node1304 := by rfl

def raw5348 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw5348step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-1, -1, -1, 3], ![1, 1, 2, -4]]

def raw5348step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![1, 1, 1, -3], ![-1, -1, -2, 4]]

def raw5348step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 1, 1, -3]]

theorem canonical5348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5348 = injectiveMoment H node757 := by
  calc
    injectiveMoment H raw5348 = injectiveMoment H raw5348step0 := by
      have heq : raw5348step0 = raw5348.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5348).symm
    injectiveMoment H raw5348step0 = injectiveMoment H raw5348step1 := by
      have heq : raw5348step1 = -raw5348step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5348step0).symm
    injectiveMoment H raw5348step1 = injectiveMoment H raw5348step2 := by
      have heq : raw5348step2 = (fun i j => raw5348step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5348step1 permutation27 permutation17
    _ = injectiveMoment H node757 := by rfl

def raw5349 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw5349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -1, -1, 3], ![1, 1, 1, -3]]

def raw5349step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

theorem canonical5349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5349 = injectiveMoment H node941 := by
  calc
    injectiveMoment H raw5349 = injectiveMoment H raw5349step0 := by
      have heq : raw5349step0 = raw5349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5349).symm
    injectiveMoment H raw5349step0 = injectiveMoment H raw5349step1 := by
      have heq : raw5349step1 = (fun i j => raw5349step0 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5349step0 permutation23 permutation17
    _ = injectiveMoment H node941 := by rfl

def raw5350 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -1, 0, 2], ![1, 1, 0, -2]]

def raw5350step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical5350 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5350 = injectiveMoment H node1244 := by
  calc
    injectiveMoment H raw5350 = injectiveMoment H raw5350step0 := by
      have heq : raw5350step0 = raw5350.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5350).symm
    injectiveMoment H raw5350step0 = injectiveMoment H raw5350step1 := by
      have heq : raw5350step1 = (fun i j => raw5350step0 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5350step0 permutation23 permutation17
    _ = injectiveMoment H node1244 := by rfl

def raw5351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -1, 1, 1], ![1, 1, -1, -1]]

def raw5351step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical5351 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5351 = injectiveMoment H node1360 := by
  calc
    injectiveMoment H raw5351 = injectiveMoment H raw5351step0 := by
      have heq : raw5351step0 = raw5351.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5351).symm
    injectiveMoment H raw5351step0 = injectiveMoment H raw5351step1 := by
      have heq : raw5351step1 = (fun i j => raw5351step0 (permutation23 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5351step0 permutation23 permutation18
    _ = injectiveMoment H node1360 := by rfl

def raw5352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5352step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, 0, 1, 1, -1], ![1, 0, -1, -1, 1]]

def raw5352step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw5352step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical5352 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5352 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw5352 = injectiveMoment H raw5352step0 := by
      have heq : raw5352step0 = raw5352.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5352).symm
    injectiveMoment H raw5352step0 = injectiveMoment H raw5352step1 := by
      have hz : ∀ i, raw5352step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw5352step1 = (fun i j => raw5352step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5352step0 permutation57 hz
    injectiveMoment H raw5352step1 = injectiveMoment H raw5352step2 := by
      have heq : raw5352step2 = (fun i j => raw5352step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5352step1 permutation27 permutation17
    _ = injectiveMoment H node1107 := by rfl

def raw5353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5353step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-1, 0, 1, -1, 1], ![1, 0, -1, 1, -1]]

def raw5353step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 1, -1, 1], ![1, -1, 1, -1]]

def raw5353step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical5353 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5353 = injectiveMoment H node1096 := by
  calc
    injectiveMoment H raw5353 = injectiveMoment H raw5353step0 := by
      have heq : raw5353step0 = raw5353.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5353).symm
    injectiveMoment H raw5353step0 = injectiveMoment H raw5353step1 := by
      have hz : ∀ i, raw5353step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw5353step1 = (fun i j => raw5353step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5353step0 permutation57 hz
    injectiveMoment H raw5353step1 = injectiveMoment H raw5353step2 := by
      have heq : raw5353step2 = (fun i j => raw5353step1 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5353step1 permutation29 permutation20
    _ = injectiveMoment H node1096 := by rfl

def raw5354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5354step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-1, 0, 2, -1, 0], ![1, 0, -2, 1, 0]]

def raw5354step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 2, -1, 0], ![1, -2, 1, 0]]

def raw5354step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical5354 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5354 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw5354 = injectiveMoment H raw5354step0 := by
      have heq : raw5354step0 = raw5354.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5354).symm
    injectiveMoment H raw5354step0 = injectiveMoment H raw5354step1 := by
      have hz : ∀ i, raw5354step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw5354step1 = (fun i j => raw5354step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5354step0 permutation57 hz
    injectiveMoment H raw5354step1 = injectiveMoment H raw5354step2 := by
      have heq : raw5354step2 = (fun i j => raw5354step1 (permutation18 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5354step1 permutation18 permutation32
    _ = injectiveMoment H node1005 := by rfl

def raw5355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![0, 0, 2, -2], ![2, -2, -1, 1]]

def raw5355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 0, 2, -1], ![1, 0, -2, 1]]

def raw5355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2], ![-1, 2, -1], ![1, -2, 1]]

def raw5355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5355 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw5355 = injectiveMoment H raw5355step0 := by
      have heq : raw5355step0 = raw5355.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5355).symm
    injectiveMoment H raw5355step0 = injectiveMoment H raw5355step1 := by
      have hz : ∀ i, raw5355step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5355step1 = (fun i j => raw5355step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5355step0 permutation15 hz
    injectiveMoment H raw5355step1 = injectiveMoment H raw5355step2 := by
      have heq : raw5355step2 = (fun i j => raw5355step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5355step1 permutation27 permutation5
    _ = injectiveMoment H node224 := by rfl

def raw5356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5356step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 0, -1, 2], ![1, 0, 1, -2]]

def raw5356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1], ![-1, -1, 2], ![1, 1, -2]]

def raw5356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical5356 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5356 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw5356 = injectiveMoment H raw5356step0 := by
      have heq : raw5356step0 = raw5356.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5356).symm
    injectiveMoment H raw5356step0 = injectiveMoment H raw5356step1 := by
      have hz : ∀ i, raw5356step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5356step1 = (fun i j => raw5356step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5356step0 permutation15 hz
    injectiveMoment H raw5356step1 = injectiveMoment H raw5356step2 := by
      have heq : raw5356step2 = (fun i j => raw5356step1 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5356step1 permutation23 permutation5
    _ = injectiveMoment H node276 := by rfl

def raw5357 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5357step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, 1, 0, 1, -1], ![1, -1, 0, -1, 1]]

def raw5357step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw5357step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical5357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5357 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw5357 = injectiveMoment H raw5357step0 := by
      have heq : raw5357step0 = raw5357.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5357).symm
    injectiveMoment H raw5357step0 = injectiveMoment H raw5357step1 := by
      have hz : ∀ i, raw5357step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw5357step1 = (fun i j => raw5357step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5357step0 permutation80 hz
    injectiveMoment H raw5357step1 = injectiveMoment H raw5357step2 := by
      have heq : raw5357step2 = (fun i j => raw5357step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5357step1 permutation27 permutation17
    _ = injectiveMoment H node1107 := by rfl

def raw5358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5358step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-1, 1, 0, -1, 1], ![1, -1, 0, 1, -1]]

def raw5358step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 1, -1, 1], ![1, -1, 1, -1]]

def raw5358step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical5358 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5358 = injectiveMoment H node1096 := by
  calc
    injectiveMoment H raw5358 = injectiveMoment H raw5358step0 := by
      have heq : raw5358step0 = raw5358.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5358).symm
    injectiveMoment H raw5358step0 = injectiveMoment H raw5358step1 := by
      have hz : ∀ i, raw5358step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw5358step1 = (fun i j => raw5358step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5358step0 permutation80 hz
    injectiveMoment H raw5358step1 = injectiveMoment H raw5358step2 := by
      have heq : raw5358step2 = (fun i j => raw5358step1 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5358step1 permutation29 permutation20
    _ = injectiveMoment H node1096 := by rfl

def raw5359 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, -2, -1, 1]]

def raw5359step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, 1, 1, 0, -1], ![1, -1, -1, 0, 1]]

def raw5359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw5359step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical5359 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5359 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw5359 = injectiveMoment H raw5359step0 := by
      have heq : raw5359step0 = raw5359.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5359).symm
    injectiveMoment H raw5359step0 = injectiveMoment H raw5359step1 := by
      have hz : ∀ i, raw5359step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw5359step1 = (fun i j => raw5359step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5359step0 permutation104 hz
    injectiveMoment H raw5359step1 = injectiveMoment H raw5359step2 := by
      have heq : raw5359step2 = (fun i j => raw5359step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5359step1 permutation27 permutation17
    _ = injectiveMoment H node1107 := by rfl

def raw5360 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -2, 2]]

def raw5360step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

theorem canonical5360 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5360 = injectiveMoment H node2345 := by
  calc
    injectiveMoment H raw5360 = injectiveMoment H raw5360step0 := by
      have heq : raw5360step0 = (fun i j => raw5360 (permutation136 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5360 permutation136 permutation15
    _ = injectiveMoment H node2345 := by rfl

def raw5361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

theorem canonical5361 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5361 = injectiveMoment H node2360 := by
  rfl

def raw5362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5362step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical5362 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5362 = injectiveMoment H node1823 := by
  calc
    injectiveMoment H raw5362 = injectiveMoment H raw5362step0 := by
      have heq : raw5362step0 = (fun i j => raw5362 (permutation33 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5362 permutation33 permutation12
    _ = injectiveMoment H node1823 := by rfl

def raw5363 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw5363step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical5363 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5363 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw5363 = injectiveMoment H raw5363step0 := by
      have heq : raw5363step0 = raw5363.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5363).symm
    injectiveMoment H raw5363step0 = injectiveMoment H raw5363step1 := by
      have heq : raw5363step1 = (fun i j => raw5363step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5363step0 permutation27 permutation17
    _ = injectiveMoment H node1107 := by rfl

def raw5364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem canonical5364 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5364 = injectiveMoment H node2361 := by
  rfl

def raw5365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem canonical5365 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5365 = injectiveMoment H node2362 := by
  rfl

def raw5366 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, -2, 2]]

def raw5366step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 2, -2], ![1, -1, -2, 2]]

def raw5366step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, -1, -2]]

theorem canonical5366 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5366 = injectiveMoment H node825 := by
  calc
    injectiveMoment H raw5366 = injectiveMoment H raw5366step0 := by
      have heq : raw5366step0 = raw5366.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5366).symm
    injectiveMoment H raw5366step0 = injectiveMoment H raw5366step1 := by
      have heq : raw5366step1 = (fun i j => raw5366step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5366step0 permutation27 permutation17
    _ = injectiveMoment H node825 := by rfl

def raw5367 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw5367step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 1, -2, 2], ![1, -1, 2, -2]]

def raw5367step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 2, -1, -2]]

theorem canonical5367 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5367 = injectiveMoment H node822 := by
  calc
    injectiveMoment H raw5367 = injectiveMoment H raw5367step0 := by
      have heq : raw5367step0 = raw5367.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5367).symm
    injectiveMoment H raw5367step0 = injectiveMoment H raw5367step1 := by
      have heq : raw5367step1 = (fun i j => raw5367step0 (permutation29 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5367step0 permutation29 permutation19
    _ = injectiveMoment H node822 := by rfl

def raw5368 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5368step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 1, -1, 1], ![1, -1, 1, -1]]

def raw5368step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical5368 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5368 = injectiveMoment H node1096 := by
  calc
    injectiveMoment H raw5368 = injectiveMoment H raw5368step0 := by
      have heq : raw5368step0 = raw5368.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5368).symm
    injectiveMoment H raw5368step0 = injectiveMoment H raw5368step1 := by
      have heq : raw5368step1 = (fun i j => raw5368step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5368step0 permutation29 permutation20
    _ = injectiveMoment H node1096 := by rfl

def raw5369 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw5369step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 1, -1], ![0, 0, -2, 2], ![-1, 2, -1, 0], ![-1, 0, 2, -1]]

def raw5369step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical5369 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5369 = injectiveMoment H node521 := by
  calc
    injectiveMoment H raw5369 = injectiveMoment H raw5369step0 := by
      have heq : raw5369step0 = -raw5369 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5369).symm
    injectiveMoment H raw5369step0 = injectiveMoment H raw5369step1 := by
      have heq : raw5369step1 = (fun i j => raw5369step0 (permutation13 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5369step0 permutation13 permutation19
    _ = injectiveMoment H node521 := by rfl

def raw5370 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw5370step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 2, -2, 1], ![1, -2, 2, -1]]

def raw5370step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, -1, -2]]

theorem canonical5370 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5370 = injectiveMoment H node503 := by
  calc
    injectiveMoment H raw5370 = injectiveMoment H raw5370step0 := by
      have heq : raw5370step0 = raw5370.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5370).symm
    injectiveMoment H raw5370step0 = injectiveMoment H raw5370step1 := by
      have heq : raw5370step1 = (fun i j => raw5370step0 (permutation29 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5370step0 permutation29 permutation19
    _ = injectiveMoment H node503 := by rfl

def raw5371 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5371step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 2, -1, 0], ![1, -2, 1, 0]]

def raw5371step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical5371 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5371 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw5371 = injectiveMoment H raw5371step0 := by
      have heq : raw5371step0 = raw5371.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5371).symm
    injectiveMoment H raw5371step0 = injectiveMoment H raw5371step1 := by
      have heq : raw5371step1 = (fun i j => raw5371step0 (permutation18 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5371step0 permutation18 permutation32
    _ = injectiveMoment H node1005 := by rfl

def raw5372 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw5372step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 2, 0, -1], ![1, -2, 0, 1]]

def raw5372step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical5372 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5372 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw5372 = injectiveMoment H raw5372step0 := by
      have heq : raw5372step0 = raw5372.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5372).symm
    injectiveMoment H raw5372step0 = injectiveMoment H raw5372step1 := by
      have heq : raw5372step1 = (fun i j => raw5372step0 (permutation18 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5372step0 permutation18 permutation26
    _ = injectiveMoment H node1005 := by rfl

def raw5373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw5373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 3, -2, 0], ![1, -3, 2, 0]]

def raw5373step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

theorem canonical5373 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5373 = injectiveMoment H node989 := by
  calc
    injectiveMoment H raw5373 = injectiveMoment H raw5373step0 := by
      have heq : raw5373step0 = raw5373.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5373).symm
    injectiveMoment H raw5373step0 = injectiveMoment H raw5373step1 := by
      have heq : raw5373step1 = (fun i j => raw5373step0 (permutation18 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5373step0 permutation18 permutation32
    _ = injectiveMoment H node989 := by rfl

def raw5374 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem canonical5374 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5374 = injectiveMoment H node720 := by
  rfl

def raw5375 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![1, -1, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw5375step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, 0, -1], ![-1, -2, 2, 1], ![1, 2, -2, -1]]

def raw5375step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, -1, -2]]

theorem canonical5375 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5375 = injectiveMoment H node503 := by
  calc
    injectiveMoment H raw5375 = injectiveMoment H raw5375step0 := by
      have heq : raw5375step0 = raw5375.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5375).symm
    injectiveMoment H raw5375step0 = injectiveMoment H raw5375step1 := by
      have heq : raw5375step1 = (fun i j => raw5375step0 (permutation29 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5375step0 permutation29 permutation25
    _ = injectiveMoment H node503 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
