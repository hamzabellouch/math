import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4352step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical4352 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4352 = injectiveMoment H node2161 := by
  calc
    injectiveMoment H raw4352 = injectiveMoment H raw4352step0 := by
      have heq : raw4352step0 = (fun i j => raw4352 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4352 permutation39 permutation9
    _ = injectiveMoment H node2161 := by rfl

def raw4353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4353step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical4353 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4353 = injectiveMoment H node2165 := by
  calc
    injectiveMoment H raw4353 = injectiveMoment H raw4353step0 := by
      have heq : raw4353step0 = (fun i j => raw4353 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4353 permutation39 permutation9
    _ = injectiveMoment H node2165 := by rfl

def raw4354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4354step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical4354 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4354 = injectiveMoment H node2167 := by
  calc
    injectiveMoment H raw4354 = injectiveMoment H raw4354step0 := by
      have heq : raw4354step0 = (fun i j => raw4354 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4354 permutation39 permutation9
    _ = injectiveMoment H node2167 := by rfl

def raw4355 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, -1, 0, -1]]

def raw4355step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 0, -1], ![-2, 1, 1, 0, 0], ![3, -1, -1, 0, -1]]

def raw4355step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![3, -1, -1, -1]]

def raw4355step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical4355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4355 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw4355 = injectiveMoment H raw4355step0 := by
      have heq : raw4355step0 = raw4355.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4355).symm
    injectiveMoment H raw4355step0 = injectiveMoment H raw4355step1 := by
      have hz : ∀ i, raw4355step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw4355step1 = (fun i j => raw4355step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4355step0 permutation104 hz
    injectiveMoment H raw4355step1 = injectiveMoment H raw4355step2 := by
      have heq : raw4355step2 = (fun i j => raw4355step1 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4355step1 permutation29 permutation18
    _ = injectiveMoment H node959 := by rfl

def raw4356 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical4356 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4356 = injectiveMoment H node2183 := by
  rfl

def raw4357 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4357step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical4357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4357 = injectiveMoment H node1507 := by
  calc
    injectiveMoment H raw4357 = injectiveMoment H raw4357step0 := by
      have heq : raw4357step0 = (fun i j => raw4357 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4357 permutation45 permutation11
    _ = injectiveMoment H node1507 := by rfl

def raw4358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

theorem canonical4358 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4358 = injectiveMoment H node2184 := by
  rfl

def raw4359 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical4359 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4359 = injectiveMoment H node2185 := by
  rfl

def raw4360 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4360step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical4360 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4360 = injectiveMoment H node2823 := by
  calc
    injectiveMoment H raw4360 = injectiveMoment H raw4360step0 := by
      have heq : raw4360step0 = (fun i j => raw4360 (permutation125 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4360 permutation125 permutation17
    _ = injectiveMoment H node2823 := by rfl

def raw4361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4361step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical4361 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4361 = injectiveMoment H node2843 := by
  calc
    injectiveMoment H raw4361 = injectiveMoment H raw4361step0 := by
      have heq : raw4361step0 = (fun i j => raw4361 (permutation113 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4361 permutation113 permutation16
    _ = injectiveMoment H node2843 := by rfl

def raw4362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem canonical4362 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4362 = injectiveMoment H node2186 := by
  rfl

def raw4363 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

theorem canonical4363 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4363 = injectiveMoment H node2187 := by
  rfl

def raw4364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, -1, -1]]

theorem canonical4364 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4364 = injectiveMoment H node2188 := by
  rfl

def raw4365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical4365 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4365 = injectiveMoment H node2850 := by
  calc
    injectiveMoment H raw4365 = injectiveMoment H raw4365step0 := by
      have heq : raw4365step0 = (fun i j => raw4365 (permutation119 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4365 permutation119 permutation16
    _ = injectiveMoment H node2850 := by rfl

def raw4366 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical4366 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4366 = injectiveMoment H node2189 := by
  rfl

def raw4367 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical4367 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4367 = injectiveMoment H node2190 := by
  rfl

def raw4368 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical4368 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4368 = injectiveMoment H node2191 := by
  rfl

def raw4369 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4369step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, -1, 2], ![3, -1, 0, -2]]

def raw4369step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 2, -2]]

theorem canonical4369 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4369 = injectiveMoment H node1219 := by
  calc
    injectiveMoment H raw4369 = injectiveMoment H raw4369step0 := by
      have heq : raw4369step0 = raw4369.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4369).symm
    injectiveMoment H raw4369step0 = injectiveMoment H raw4369step1 := by
      have heq : raw4369step1 = (fun i j => raw4369step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4369step0 permutation27 permutation18
    _ = injectiveMoment H node1219 := by rfl

def raw4370 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4370step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical4370 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4370 = injectiveMoment H node1508 := by
  calc
    injectiveMoment H raw4370 = injectiveMoment H raw4370step0 := by
      have heq : raw4370step0 = (fun i j => raw4370 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4370 permutation40 permutation11
    _ = injectiveMoment H node1508 := by rfl

def raw4371 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical4371 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4371 = injectiveMoment H node2192 := by
  rfl

def raw4372 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4372step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical4372 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4372 = injectiveMoment H node1506 := by
  calc
    injectiveMoment H raw4372 = injectiveMoment H raw4372step0 := by
      have heq : raw4372step0 = (fun i j => raw4372 (permutation41 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4372 permutation41 permutation21
    _ = injectiveMoment H node1506 := by rfl

def raw4373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, 0, 1], ![3, -1, -1, -1]]

def raw4373step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical4373 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4373 = injectiveMoment H node973 := by
  calc
    injectiveMoment H raw4373 = injectiveMoment H raw4373step0 := by
      have heq : raw4373step0 = raw4373.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4373).symm
    injectiveMoment H raw4373step0 = injectiveMoment H raw4373step1 := by
      have heq : raw4373step1 = (fun i j => raw4373step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4373step0 permutation27 permutation18
    _ = injectiveMoment H node973 := by rfl

def raw4374 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem canonical4374 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4374 = injectiveMoment H node2193 := by
  rfl

def raw4375 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical4375 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4375 = injectiveMoment H node2194 := by
  rfl

def raw4376 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4376step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical4376 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4376 = injectiveMoment H node1512 := by
  calc
    injectiveMoment H raw4376 = injectiveMoment H raw4376step0 := by
      have heq : raw4376step0 = (fun i j => raw4376 (permutation49 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4376 permutation49 permutation21
    _ = injectiveMoment H node1512 := by rfl

def raw4377 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw4377step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, 1, 0], ![3, -1, -2, 0]]

def raw4377step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical4377 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4377 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw4377 = injectiveMoment H raw4377step0 := by
      have heq : raw4377step0 = raw4377.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4377).symm
    injectiveMoment H raw4377step0 = injectiveMoment H raw4377step1 := by
      have heq : raw4377step1 = (fun i j => raw4377step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4377step0 permutation27 permutation18
    _ = injectiveMoment H node804 := by rfl

def raw4378 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4378 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4378 = injectiveMoment H node2195 := by
  rfl

def raw4379 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4379step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4379 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4379 = injectiveMoment H node2195 := by
  calc
    injectiveMoment H raw4379 = injectiveMoment H raw4379step0 := by
      have heq : raw4379step0 = (fun i j => raw4379 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4379 permutation34 permutation9
    _ = injectiveMoment H node2195 := by rfl

def raw4380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw4380step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, 2, -1], ![3, -1, -3, 1]]

def raw4380step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 2, -1, -2]]

theorem canonical4380 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4380 = injectiveMoment H node725 := by
  calc
    injectiveMoment H raw4380 = injectiveMoment H raw4380step0 := by
      have heq : raw4380step0 = raw4380.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4380).symm
    injectiveMoment H raw4380step0 = injectiveMoment H raw4380step1 := by
      have heq : raw4380step1 = (fun i j => raw4380step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4380step0 permutation27 permutation18
    _ = injectiveMoment H node725 := by rfl

def raw4381 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw4381step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![3, -1, 1, -3]]

def raw4381step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![2, -1, 0, -1], ![-3, 1, -1, 3]]

def raw4381step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem canonical4381 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4381 = injectiveMoment H node1239 := by
  calc
    injectiveMoment H raw4381 = injectiveMoment H raw4381step0 := by
      have heq : raw4381step0 = raw4381.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4381).symm
    injectiveMoment H raw4381step0 = injectiveMoment H raw4381step1 := by
      have heq : raw4381step1 = -raw4381step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4381step0).symm
    injectiveMoment H raw4381step1 = injectiveMoment H raw4381step2 := by
      have heq : raw4381step2 = (fun i j => raw4381step1 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4381step1 permutation21 permutation18
    _ = injectiveMoment H node1239 := by rfl

def raw4382 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 1, 1, 0], ![3, -1, 0, -2]]

def raw4382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical4382 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4382 = injectiveMoment H node815 := by
  calc
    injectiveMoment H raw4382 = injectiveMoment H raw4382step0 := by
      have heq : raw4382step0 = raw4382.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4382).symm
    injectiveMoment H raw4382step0 = injectiveMoment H raw4382step1 := by
      have heq : raw4382step1 = (fun i j => raw4382step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4382step0 permutation29 permutation20
    _ = injectiveMoment H node815 := by rfl

def raw4383 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw4383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 1, 2, -1], ![3, -1, -1, -1]]

def raw4383step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical4383 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4383 = injectiveMoment H node983 := by
  calc
    injectiveMoment H raw4383 = injectiveMoment H raw4383step0 := by
      have heq : raw4383step0 = raw4383.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4383).symm
    injectiveMoment H raw4383step0 = injectiveMoment H raw4383step1 := by
      have heq : raw4383step1 = (fun i j => raw4383step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4383step0 permutation29 permutation20
    _ = injectiveMoment H node983 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
