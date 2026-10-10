import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw5408step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -1, 2, -1], ![0, 2, -2, 0]]

def raw5408step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5408 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5408 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw5408 = injectiveMoment H raw5408step0 := by
      have heq : raw5408step0 = raw5408.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5408).symm
    injectiveMoment H raw5408step0 = injectiveMoment H raw5408step1 := by
      have heq : raw5408step1 = (fun i j => raw5408step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5408step0 permutation24 permutation29
    _ = injectiveMoment H node1010 := by rfl

def raw5409 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw5409step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -1, 3, -2], ![0, 2, -3, 1]]

def raw5409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

theorem canonical5409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5409 = injectiveMoment H node475 := by
  calc
    injectiveMoment H raw5409 = injectiveMoment H raw5409step0 := by
      have heq : raw5409step0 = raw5409.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5409).symm
    injectiveMoment H raw5409step0 = injectiveMoment H raw5409step1 := by
      have heq : raw5409step1 = (fun i j => raw5409step0 (permutation23 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5409step0 permutation23 permutation29
    _ = injectiveMoment H node475 := by rfl

def raw5410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw5410step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical5410 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5410 = injectiveMoment H node1632 := by
  calc
    injectiveMoment H raw5410 = injectiveMoment H raw5410step0 := by
      have heq : raw5410step0 = (fun i j => raw5410 (permutation72 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5410 permutation72 permutation29
    _ = injectiveMoment H node1632 := by rfl

def raw5411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw5411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, 3, -2, -1], ![0, -2, 2, 0]]

def raw5411step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

theorem canonical5411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5411 = injectiveMoment H node1223 := by
  calc
    injectiveMoment H raw5411 = injectiveMoment H raw5411step0 := by
      have heq : raw5411step0 = raw5411.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5411).symm
    injectiveMoment H raw5411step0 = injectiveMoment H raw5411step1 := by
      have heq : raw5411step1 = (fun i j => raw5411step0 (permutation26 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5411step0 permutation26 permutation28
    _ = injectiveMoment H node1223 := by rfl

def raw5412 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw5412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, 3, -1, -2], ![0, -2, 1, 1]]

def raw5412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical5412 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5412 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw5412 = injectiveMoment H raw5412step0 := by
      have heq : raw5412step0 = raw5412.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5412).symm
    injectiveMoment H raw5412step0 = injectiveMoment H raw5412step1 := by
      have heq : raw5412step1 = (fun i j => raw5412step0 (permutation23 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5412step0 permutation23 permutation31
    _ = injectiveMoment H node476 := by rfl

def raw5413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw5413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, 3, 0, -3], ![0, -2, 0, 2]]

def raw5413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

theorem canonical5413 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5413 = injectiveMoment H node1374 := by
  calc
    injectiveMoment H raw5413 = injectiveMoment H raw5413step0 := by
      have heq : raw5413step0 = raw5413.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5413).symm
    injectiveMoment H raw5413step0 = injectiveMoment H raw5413step1 := by
      have heq : raw5413step1 = (fun i j => raw5413step0 (permutation20 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5413step0 permutation20 permutation21
    _ = injectiveMoment H node1374 := by rfl

def raw5414 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical5414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5414 = injectiveMoment H node2370 := by
  rfl

def raw5415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5415step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -3, 0, 3], ![0, 3, 0, -3]]

def raw5415step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, -2, 0, 1]]

theorem canonical5415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5415 = injectiveMoment H node1375 := by
  calc
    injectiveMoment H raw5415 = injectiveMoment H raw5415step0 := by
      have heq : raw5415step0 = raw5415.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5415).symm
    injectiveMoment H raw5415step0 = injectiveMoment H raw5415step1 := by
      have heq : raw5415step1 = (fun i j => raw5415step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5415step0 permutation18 permutation21
    _ = injectiveMoment H node1375 := by rfl

def raw5416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -3, 3], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -3, 1, 2], ![0, 3, -1, -2]]

def raw5416step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]

theorem canonical5416 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5416 = injectiveMoment H node689 := by
  calc
    injectiveMoment H raw5416 = injectiveMoment H raw5416step0 := by
      have heq : raw5416step0 = raw5416.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5416).symm
    injectiveMoment H raw5416step0 = injectiveMoment H raw5416step1 := by
      have heq : raw5416step1 = (fun i j => raw5416step0 (permutation14 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5416step0 permutation14 permutation11
    _ = injectiveMoment H node689 := by rfl

def raw5417 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical5417 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5417 = injectiveMoment H node2371 := by
  rfl

def raw5418 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5418step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![0, -2, 0, 0, 2], ![0, 2, 0, 0, -2]]

def raw5418step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -2, 0, 2], ![0, 2, 0, -2]]

def raw5418step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5418 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5418 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw5418 = injectiveMoment H raw5418step0 := by
      have heq : raw5418step0 = raw5418.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5418).symm
    injectiveMoment H raw5418step0 = injectiveMoment H raw5418step1 := by
      have hz : ∀ i, raw5418step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw5418step1 = (fun i j => raw5418step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5418step0 permutation80 hz
    injectiveMoment H raw5418step1 = injectiveMoment H raw5418step2 := by
      have heq : raw5418step2 = (fun i j => raw5418step1 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5418step1 permutation18 permutation23
    _ = injectiveMoment H node1304 := by rfl

def raw5419 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem canonical5419 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5419 = injectiveMoment H node2372 := by
  rfl

def raw5420 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5420step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical5420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5420 = injectiveMoment H node2000 := by
  calc
    injectiveMoment H raw5420 = injectiveMoment H raw5420step0 := by
      have heq : raw5420step0 = (fun i j => raw5420 (permutation33 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5420 permutation33 permutation12
    _ = injectiveMoment H node2000 := by rfl

def raw5421 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5421step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![0, -2, 1, 1], ![0, 2, -1, -1]]

def raw5421step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5421 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5421 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw5421 = injectiveMoment H raw5421step0 := by
      have heq : raw5421step0 = raw5421.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5421).symm
    injectiveMoment H raw5421step0 = injectiveMoment H raw5421step1 := by
      have heq : raw5421step1 = (fun i j => raw5421step0 (permutation27 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5421step0 permutation27 permutation21
    _ = injectiveMoment H node1304 := by rfl

def raw5422 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5422step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical5422 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5422 = injectiveMoment H node1998 := by
  calc
    injectiveMoment H raw5422 = injectiveMoment H raw5422step0 := by
      have heq : raw5422step0 = (fun i j => raw5422 (permutation60 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5422 permutation60 permutation21
    _ = injectiveMoment H node1998 := by rfl

def raw5423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical5423 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5423 = injectiveMoment H node605 := by
  calc
    injectiveMoment H raw5423 = injectiveMoment H raw5423step0 := by
      have heq : raw5423step0 = (fun i j => raw5423 (permutation9 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5423 permutation9 permutation12
    _ = injectiveMoment H node605 := by rfl

def raw5424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw5424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -2, -1, 3], ![0, 2, 1, -3]]

def raw5424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem canonical5424 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5424 = injectiveMoment H node471 := by
  calc
    injectiveMoment H raw5424 = injectiveMoment H raw5424step0 := by
      have heq : raw5424step0 = raw5424.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5424).symm
    injectiveMoment H raw5424step0 = injectiveMoment H raw5424step1 := by
      have heq : raw5424step1 = (fun i j => raw5424step0 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5424step0 permutation23 permutation17
    _ = injectiveMoment H node471 := by rfl

def raw5425 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5425step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -2, 0, 2], ![0, 2, 0, -2]]

def raw5425step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5425 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5425 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw5425 = injectiveMoment H raw5425step0 := by
      have heq : raw5425step0 = raw5425.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5425).symm
    injectiveMoment H raw5425step0 = injectiveMoment H raw5425step1 := by
      have heq : raw5425step1 = (fun i j => raw5425step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5425step0 permutation18 permutation23
    _ = injectiveMoment H node1304 := by rfl

def raw5426 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5426step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical5426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5426 = injectiveMoment H node608 := by
  calc
    injectiveMoment H raw5426 = injectiveMoment H raw5426step0 := by
      have heq : raw5426step0 = (fun i j => raw5426 (permutation9 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5426 permutation9 permutation12
    _ = injectiveMoment H node608 := by rfl

def raw5427 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw5427step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical5427 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5427 = injectiveMoment H node2369 := by
  calc
    injectiveMoment H raw5427 = injectiveMoment H raw5427step0 := by
      have heq : raw5427step0 = (fun i j => raw5427 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5427 permutation39 permutation9
    _ = injectiveMoment H node2369 := by rfl

def raw5428 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5428step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical5428 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5428 = injectiveMoment H node2371 := by
  calc
    injectiveMoment H raw5428 = injectiveMoment H raw5428step0 := by
      have heq : raw5428step0 = (fun i j => raw5428 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5428 permutation39 permutation9
    _ = injectiveMoment H node2371 := by rfl

def raw5429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw5429step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical5429 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5429 = injectiveMoment H node1507 := by
  calc
    injectiveMoment H raw5429 = injectiveMoment H raw5429step0 := by
      have heq : raw5429step0 = (fun i j => raw5429 (permutation125 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5429 permutation125 permutation19
    _ = injectiveMoment H node1507 := by rfl

def raw5430 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical5430 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5430 = injectiveMoment H node2373 := by
  rfl

def raw5431 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5431step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical5431 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5431 = injectiveMoment H node1752 := by
  calc
    injectiveMoment H raw5431 = injectiveMoment H raw5431step0 := by
      have heq : raw5431step0 = (fun i j => raw5431 (permutation145 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5431 permutation145 permutation29
    _ = injectiveMoment H node1752 := by rfl

def raw5432 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, -1, -1, 1]]

def raw5432step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical5432 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5432 = injectiveMoment H node2373 := by
  calc
    injectiveMoment H raw5432 = injectiveMoment H raw5432step0 := by
      have heq : raw5432step0 = (fun i j => raw5432 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5432 permutation34 permutation9
    _ = injectiveMoment H node2373 := by rfl

def raw5433 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5433step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![0, -1, 0, -1, 2], ![0, 1, 0, 1, -2]]

def raw5433step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2]]

def raw5433step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical5433 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5433 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw5433 = injectiveMoment H raw5433step0 := by
      have heq : raw5433step0 = raw5433.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5433).symm
    injectiveMoment H raw5433step0 = injectiveMoment H raw5433step1 := by
      have hz : ∀ i, raw5433step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw5433step1 = (fun i j => raw5433step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5433step0 permutation80 hz
    injectiveMoment H raw5433step1 = injectiveMoment H raw5433step2 := by
      have heq : raw5433step2 = (fun i j => raw5433step1 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5433step1 permutation23 permutation17
    _ = injectiveMoment H node1005 := by rfl

def raw5434 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

theorem canonical5434 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5434 = injectiveMoment H node2374 := by
  rfl

def raw5435 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5435step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical5435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5435 = injectiveMoment H node2017 := by
  calc
    injectiveMoment H raw5435 = injectiveMoment H raw5435step0 := by
      have heq : raw5435step0 = (fun i j => raw5435 (permutation33 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5435 permutation33 permutation12
    _ = injectiveMoment H node2017 := by rfl

def raw5436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, -1, 3, -3]]

def raw5436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -1, -2, 3], ![0, 1, 2, -3]]

def raw5436step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical5436 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5436 = injectiveMoment H node1188 := by
  calc
    injectiveMoment H raw5436 = injectiveMoment H raw5436step0 := by
      have heq : raw5436step0 = raw5436.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5436).symm
    injectiveMoment H raw5436step0 = injectiveMoment H raw5436step1 := by
      have heq : raw5436step1 = (fun i j => raw5436step0 (permutation21 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5436step0 permutation21 permutation15
    _ = injectiveMoment H node1188 := by rfl

def raw5437 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5437step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2]]

def raw5437step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical5437 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5437 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw5437 = injectiveMoment H raw5437step0 := by
      have heq : raw5437step0 = raw5437.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5437).symm
    injectiveMoment H raw5437step0 = injectiveMoment H raw5437step1 := by
      have heq : raw5437step1 = (fun i j => raw5437step0 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5437step0 permutation23 permutation17
    _ = injectiveMoment H node1005 := by rfl

def raw5438 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 0, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw5438step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, 0, -2, 2], ![0, 0, 2, -2]]

def raw5438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1], ![0, -2, 2], ![0, 2, -2]]

def raw5438step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5438 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5438 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw5438 = injectiveMoment H raw5438step0 := by
      have heq : raw5438step0 = raw5438.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5438).symm
    injectiveMoment H raw5438step0 = injectiveMoment H raw5438step1 := by
      have hz : ∀ i, raw5438step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5438step1 = (fun i j => raw5438step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5438step0 permutation15 hz
    injectiveMoment H raw5438step1 = injectiveMoment H raw5438step2 := by
      have heq : raw5438step2 = (fun i j => raw5438step1 (permutation12 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5438step1 permutation12 permutation3
    _ = injectiveMoment H node224 := by rfl

def raw5439 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, -1, 2, -2]]

def raw5439step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, 1, -3, 2], ![0, -1, 3, -2]]

def raw5439step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical5439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5439 = injectiveMoment H node1188 := by
  calc
    injectiveMoment H raw5439 = injectiveMoment H raw5439step0 := by
      have heq : raw5439step0 = raw5439.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5439).symm
    injectiveMoment H raw5439step0 = injectiveMoment H raw5439step1 := by
      have heq : raw5439step1 = (fun i j => raw5439step0 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5439step0 permutation27 permutation16
    _ = injectiveMoment H node1188 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
