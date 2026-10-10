import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4512 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical4512 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4512 = injectiveMoment H node2220 := by
  rfl

def raw4513 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]

theorem canonical4513 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4513 = injectiveMoment H node2221 := by
  rfl

def raw4514 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4514step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

theorem canonical4514 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4514 = injectiveMoment H node2853 := by
  calc
    injectiveMoment H raw4514 = injectiveMoment H raw4514step0 := by
      have heq : raw4514step0 = (fun i j => raw4514 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4514 permutation113 permutation15
    _ = injectiveMoment H node2853 := by rfl

def raw4515 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw4515step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -1, 2]]

theorem canonical4515 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4515 = injectiveMoment H node2858 := by
  calc
    injectiveMoment H raw4515 = injectiveMoment H raw4515step0 := by
      have heq : raw4515step0 = (fun i j => raw4515 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4515 permutation113 permutation15
    _ = injectiveMoment H node2858 := by rfl

def raw4516 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4516step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, -1, 0, 0, 2], ![2, 1, 0, -1, -2]]

def raw4516step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 0, 2], ![2, 1, -1, -2]]

def raw4516step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical4516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4516 = injectiveMoment H node1253 := by
  calc
    injectiveMoment H raw4516 = injectiveMoment H raw4516step0 := by
      have heq : raw4516step0 = raw4516.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4516).symm
    injectiveMoment H raw4516step0 = injectiveMoment H raw4516step1 := by
      have hz : ∀ i, raw4516step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw4516step1 = (fun i j => raw4516step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4516step0 permutation80 hz
    injectiveMoment H raw4516step1 = injectiveMoment H raw4516step2 := by
      have heq : raw4516step2 = (fun i j => raw4516step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4516step1 permutation21 permutation17
    _ = injectiveMoment H node1253 := by rfl

def raw4517 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical4517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4517 = injectiveMoment H node2222 := by
  rfl

def raw4518 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4518step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical4518 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4518 = injectiveMoment H node1737 := by
  calc
    injectiveMoment H raw4518 = injectiveMoment H raw4518step0 := by
      have heq : raw4518step0 = (fun i j => raw4518 (permutation35 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4518 permutation35 permutation11
    _ = injectiveMoment H node1737 := by rfl

def raw4519 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

theorem canonical4519 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4519 = injectiveMoment H node2223 := by
  rfl

def raw4520 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4520step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical4520 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4520 = injectiveMoment H node2817 := by
  calc
    injectiveMoment H raw4520 = injectiveMoment H raw4520step0 := by
      have heq : raw4520step0 = (fun i j => raw4520 (permutation113 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4520 permutation113 permutation17
    _ = injectiveMoment H node2817 := by rfl

def raw4521 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4521step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical4521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4521 = injectiveMoment H node2857 := by
  calc
    injectiveMoment H raw4521 = injectiveMoment H raw4521step0 := by
      have heq : raw4521step0 = (fun i j => raw4521 (permutation115 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4521 permutation115 permutation17
    _ = injectiveMoment H node2857 := by rfl

def raw4522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical4522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4522 = injectiveMoment H node2224 := by
  rfl

def raw4523 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical4523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4523 = injectiveMoment H node2225 := by
  rfl

def raw4524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4524step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical4524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4524 = injectiveMoment H node2814 := by
  calc
    injectiveMoment H raw4524 = injectiveMoment H raw4524step0 := by
      have heq : raw4524step0 = (fun i j => raw4524 (permutation115 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4524 permutation115 permutation17
    _ = injectiveMoment H node2814 := by rfl

def raw4525 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical4525 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4525 = injectiveMoment H node2226 := by
  rfl

def raw4526 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical4526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4526 = injectiveMoment H node2228 := by
  rfl

def raw4527 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw4527step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, -1, 3], ![2, 1, 0, -3]]

def raw4527step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 2, -3]]

theorem canonical4527 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4527 = injectiveMoment H node958 := by
  calc
    injectiveMoment H raw4527 = injectiveMoment H raw4527step0 := by
      have heq : raw4527step0 = raw4527.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4527).symm
    injectiveMoment H raw4527step0 = injectiveMoment H raw4527step1 := by
      have heq : raw4527step1 = (fun i j => raw4527step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4527step0 permutation21 permutation17
    _ = injectiveMoment H node958 := by rfl

def raw4528 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4528step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem canonical4528 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4528 = injectiveMoment H node1738 := by
  calc
    injectiveMoment H raw4528 = injectiveMoment H raw4528step0 := by
      have heq : raw4528step0 = (fun i j => raw4528 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4528 permutation34 permutation11
    _ = injectiveMoment H node1738 := by rfl

def raw4529 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4529step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 0, 2], ![2, 1, -1, -2]]

def raw4529step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical4529 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4529 = injectiveMoment H node1253 := by
  calc
    injectiveMoment H raw4529 = injectiveMoment H raw4529step0 := by
      have heq : raw4529step0 = raw4529.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4529).symm
    injectiveMoment H raw4529step0 = injectiveMoment H raw4529step1 := by
      have heq : raw4529step1 = (fun i j => raw4529step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4529step0 permutation21 permutation17
    _ = injectiveMoment H node1253 := by rfl

def raw4530 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4530step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4530step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical4530 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4530 = injectiveMoment H node1716 := by
  calc
    injectiveMoment H raw4530 = injectiveMoment H raw4530step0 := by
      have heq : raw4530step0 = -raw4530 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4530).symm
    injectiveMoment H raw4530step0 = injectiveMoment H raw4530step1 := by
      have heq : raw4530step1 = (fun i j => raw4530step0 (permutation96 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4530step0 permutation96 permutation23
    _ = injectiveMoment H node1716 := by rfl

def raw4531 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4531step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 2, 0], ![2, 1, -3, 0]]

def raw4531step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 1, -2, 0], ![-2, -1, 3, 0]]

def raw4531step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical4531 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4531 = injectiveMoment H node1190 := by
  calc
    injectiveMoment H raw4531 = injectiveMoment H raw4531step0 := by
      have heq : raw4531step0 = raw4531.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4531).symm
    injectiveMoment H raw4531step0 = injectiveMoment H raw4531step1 := by
      have heq : raw4531step1 = -raw4531step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4531step0).symm
    injectiveMoment H raw4531step1 = injectiveMoment H raw4531step2 := by
      have heq : raw4531step2 = (fun i j => raw4531step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4531step1 permutation27 permutation19
    _ = injectiveMoment H node1190 := by rfl

def raw4532 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4532 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4532 = injectiveMoment H node2231 := by
  rfl

def raw4533 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4533step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4533 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4533 = injectiveMoment H node2231 := by
  calc
    injectiveMoment H raw4533 = injectiveMoment H raw4533step0 := by
      have heq : raw4533step0 = (fun i j => raw4533 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4533 permutation34 permutation9
    _ = injectiveMoment H node2231 := by rfl

def raw4534 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw4534step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 3, -1], ![2, 1, -4, 1]]

def raw4534step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 1, -3, 1], ![-2, -1, 4, -1]]

def raw4534step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 1, 1, -3]]

theorem canonical4534 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4534 = injectiveMoment H node757 := by
  calc
    injectiveMoment H raw4534 = injectiveMoment H raw4534step0 := by
      have heq : raw4534step0 = raw4534.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4534).symm
    injectiveMoment H raw4534step0 = injectiveMoment H raw4534step1 := by
      have heq : raw4534step1 = -raw4534step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4534step0).symm
    injectiveMoment H raw4534step1 = injectiveMoment H raw4534step2 := by
      have heq : raw4534step2 = (fun i j => raw4534step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4534step1 permutation29 permutation16
    _ = injectiveMoment H node757 := by rfl

def raw4535 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw4535step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![2, 1, 1, -4]]

def raw4535step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw4535step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical4535 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4535 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw4535 = injectiveMoment H raw4535step0 := by
      have heq : raw4535step0 = raw4535.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4535).symm
    injectiveMoment H raw4535step0 = injectiveMoment H raw4535step1 := by
      have heq : raw4535step1 = -raw4535step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4535step0).symm
    injectiveMoment H raw4535step1 = injectiveMoment H raw4535step2 := by
      have heq : raw4535step2 = (fun i j => raw4535step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4535step1 permutation27 permutation17
    _ = injectiveMoment H node896 := by rfl

def raw4536 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4536step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -1, 1, 1], ![2, 1, 0, -3]]

def raw4536step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![1, 1, -1, -1], ![-2, -1, 0, 3]]

def raw4536step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical4536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4536 = injectiveMoment H node1208 := by
  calc
    injectiveMoment H raw4536 = injectiveMoment H raw4536step0 := by
      have heq : raw4536step0 = raw4536.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4536).symm
    injectiveMoment H raw4536step0 = injectiveMoment H raw4536step1 := by
      have heq : raw4536step1 = -raw4536step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4536step0).symm
    injectiveMoment H raw4536step1 = injectiveMoment H raw4536step2 := by
      have heq : raw4536step2 = (fun i j => raw4536step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4536step1 permutation27 permutation17
    _ = injectiveMoment H node1208 := by rfl

def raw4537 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4537step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -1, 2, 0], ![2, 1, -1, -2]]

def raw4537step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical4537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4537 = injectiveMoment H node1276 := by
  calc
    injectiveMoment H raw4537 = injectiveMoment H raw4537step0 := by
      have heq : raw4537step0 = raw4537.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4537).symm
    injectiveMoment H raw4537step0 = injectiveMoment H raw4537step1 := by
      have heq : raw4537step1 = (fun i j => raw4537step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4537step0 permutation21 permutation19
    _ = injectiveMoment H node1276 := by rfl

def raw4538 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4538step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![2, 1, 1, -4]]

def raw4538step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![-2, -1, -1, 4]]

def raw4538step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

theorem canonical4538 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4538 = injectiveMoment H node893 := by
  calc
    injectiveMoment H raw4538 = injectiveMoment H raw4538step0 := by
      have heq : raw4538step0 = raw4538.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4538).symm
    injectiveMoment H raw4538step0 = injectiveMoment H raw4538step1 := by
      have heq : raw4538step1 = -raw4538step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4538step0).symm
    injectiveMoment H raw4538step1 = injectiveMoment H raw4538step2 := by
      have heq : raw4538step2 = (fun i j => raw4538step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4538step1 permutation27 permutation17
    _ = injectiveMoment H node893 := by rfl

def raw4539 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4539step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw4539step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw4539step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical4539 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4539 = injectiveMoment H node1206 := by
  calc
    injectiveMoment H raw4539 = injectiveMoment H raw4539step0 := by
      have heq : raw4539step0 = raw4539.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4539).symm
    injectiveMoment H raw4539step0 = injectiveMoment H raw4539step1 := by
      have heq : raw4539step1 = -raw4539step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4539step0).symm
    injectiveMoment H raw4539step1 = injectiveMoment H raw4539step2 := by
      have heq : raw4539step2 = (fun i j => raw4539step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4539step1 permutation27 permutation17
    _ = injectiveMoment H node1206 := by rfl

def raw4540 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw4540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical4540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4540 = injectiveMoment H node1362 := by
  calc
    injectiveMoment H raw4540 = injectiveMoment H raw4540step0 := by
      have heq : raw4540step0 = (fun i j => raw4540 (permutation24 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4540 permutation24 permutation17
    _ = injectiveMoment H node1362 := by rfl

def raw4541 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw4541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -1, 2, 0], ![2, 1, -2, -1]]

def raw4541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

theorem canonical4541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4541 = injectiveMoment H node1261 := by
  calc
    injectiveMoment H raw4541 = injectiveMoment H raw4541step0 := by
      have heq : raw4541step0 = raw4541.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4541).symm
    injectiveMoment H raw4541step0 = injectiveMoment H raw4541step1 := by
      have heq : raw4541step1 = (fun i j => raw4541step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4541step0 permutation23 permutation19
    _ = injectiveMoment H node1261 := by rfl

def raw4542 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4542step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, 0, 1, -1, 1], ![2, 0, -1, 0, -1]]

def raw4542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -1, 1], ![2, -1, 0, -1]]

def raw4542step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

theorem canonical4542 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4542 = injectiveMoment H node1263 := by
  calc
    injectiveMoment H raw4542 = injectiveMoment H raw4542step0 := by
      have heq : raw4542step0 = raw4542.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4542).symm
    injectiveMoment H raw4542step0 = injectiveMoment H raw4542step1 := by
      have hz : ∀ i, raw4542step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw4542step1 = (fun i j => raw4542step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4542step0 permutation57 hz
    injectiveMoment H raw4542step1 = injectiveMoment H raw4542step2 := by
      have heq : raw4542step2 = (fun i j => raw4542step1 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4542step1 permutation27 permutation18
    _ = injectiveMoment H node1263 := by rfl

def raw4543 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4543step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, 0, 2, -1, 0], ![2, 0, -2, 0, 0]]

def raw4543step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, -1, 0], ![2, -2, 0, 0]]

def raw4543step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

theorem canonical4543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4543 = injectiveMoment H node1314 := by
  calc
    injectiveMoment H raw4543 = injectiveMoment H raw4543step0 := by
      have heq : raw4543step0 = raw4543.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4543).symm
    injectiveMoment H raw4543step0 = injectiveMoment H raw4543step1 := by
      have hz : ∀ i, raw4543step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw4543step1 = (fun i j => raw4543step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4543step0 permutation57 hz
    injectiveMoment H raw4543step1 = injectiveMoment H raw4543step2 := by
      have heq : raw4543step2 = (fun i j => raw4543step1 (permutation25 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4543step1 permutation25 permutation26
    _ = injectiveMoment H node1314 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
