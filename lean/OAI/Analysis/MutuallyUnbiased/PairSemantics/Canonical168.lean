import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5376 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![1, -1, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw5376step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, 0, -1], ![-1, -2, 3, 0], ![1, 2, -3, 0]]

def raw5376step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

theorem canonical5376 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5376 = injectiveMoment H node989 := by
  calc
    injectiveMoment H raw5376 = injectiveMoment H raw5376step0 := by
      have heq : raw5376step0 = raw5376.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5376).symm
    injectiveMoment H raw5376step0 = injectiveMoment H raw5376step1 := by
      have heq : raw5376step1 = (fun i j => raw5376step0 (permutation18 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5376step0 permutation18 permutation30
    _ = injectiveMoment H node989 := by rfl

def raw5377 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw5377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw5377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5377 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5377 = injectiveMoment H node705 := by
  calc
    injectiveMoment H raw5377 = injectiveMoment H raw5377step0 := by
      have heq : raw5377step0 = -raw5377 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5377).symm
    injectiveMoment H raw5377step0 = injectiveMoment H raw5377step1 := by
      have heq : raw5377step1 = (fun i j => raw5377step0 (permutation59 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5377step0 permutation59 permutation8
    _ = injectiveMoment H node705 := by rfl

def raw5378 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical5378 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5378 = injectiveMoment H node662 := by
  calc
    injectiveMoment H raw5378 = injectiveMoment H raw5378step0 := by
      have heq : raw5378step0 = (fun i j => raw5378 (permutation40 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5378 permutation40 permutation4
    _ = injectiveMoment H node662 := by rfl

def raw5379 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical5379 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5379 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw5379 = injectiveMoment H raw5379step0 := by
      have heq : raw5379step0 = (fun i j => raw5379 (permutation39 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5379 permutation39 permutation4
    _ = injectiveMoment H node663 := by rfl

def raw5380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5380 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5380 = injectiveMoment H node648 := by
  calc
    injectiveMoment H raw5380 = injectiveMoment H raw5380step0 := by
      have heq : raw5380step0 = (fun i j => raw5380 (permutation40 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5380 permutation40 permutation4
    _ = injectiveMoment H node648 := by rfl

def raw5381 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![1, -1, 0], ![1, 2, -3]]

def raw5381step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical5381 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5381 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw5381 = injectiveMoment H raw5381step0 := by
      have heq : raw5381step0 = (fun i j => raw5381 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5381 permutation10 permutation4
    _ = injectiveMoment H node214 := by rfl

def raw5382 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![1, 0, -1], ![1, 1, -2]]

def raw5382step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical5382 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5382 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw5382 = injectiveMoment H raw5382step0 := by
      have heq : raw5382step0 = (fun i j => raw5382 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5382 permutation10 permutation4
    _ = injectiveMoment H node215 := by rfl

def raw5383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5383 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5383 = injectiveMoment H node661 := by
  calc
    injectiveMoment H raw5383 = injectiveMoment H raw5383step0 := by
      have heq : raw5383step0 = (fun i j => raw5383 (permutation40 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5383 permutation40 permutation4
    _ = injectiveMoment H node661 := by rfl

def raw5384 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]

def raw5384step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5384 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5384 = injectiveMoment H raw5384step0 := by
      have heq : raw5384step0 = (fun i j => raw5384 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5384 permutation11 permutation4
    _ = injectiveMoment H node203 := by rfl

def raw5385 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]

def raw5385step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2]]

def raw5385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5385 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5385 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5385 = injectiveMoment H raw5385step0 := by
      have heq : raw5385step0 = -raw5385 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5385).symm
    injectiveMoment H raw5385step0 = injectiveMoment H raw5385step1 := by
      have heq : raw5385step1 = (fun i j => raw5385step0 (permutation17 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5385step0 permutation17 permutation7
    _ = injectiveMoment H node203 := by rfl

def raw5386 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5386step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical5386 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5386 = injectiveMoment H node1471 := by
  calc
    injectiveMoment H raw5386 = injectiveMoment H raw5386step0 := by
      have heq : raw5386step0 = (fun i j => raw5386 (permutation71 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5386 permutation71 permutation17
    _ = injectiveMoment H node1471 := by rfl

def raw5387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical5387 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5387 = injectiveMoment H node2363 := by
  rfl

def raw5388 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 2, -1], ![2, 0, 1, -3]]

def raw5388step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 0, 0], ![0, 1, 3, -4], ![0, 1, -2, 1], ![-2, 0, -1, 3]]

def raw5388step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical5388 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5388 = injectiveMoment H node595 := by
  calc
    injectiveMoment H raw5388 = injectiveMoment H raw5388step0 := by
      have heq : raw5388step0 = -raw5388 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5388).symm
    injectiveMoment H raw5388step0 = injectiveMoment H raw5388step1 := by
      have heq : raw5388step1 = (fun i j => raw5388step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5388step0 permutation32 permutation9
    _ = injectiveMoment H node595 := by rfl

def raw5389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical5389 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5389 = injectiveMoment H node2364 := by
  rfl

def raw5390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical5390 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5390 = injectiveMoment H node2365 := by
  rfl

def raw5391 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical5391 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5391 = injectiveMoment H node2366 := by
  rfl

def raw5392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw5392step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical5392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5392 = injectiveMoment H node2366 := by
  calc
    injectiveMoment H raw5392 = injectiveMoment H raw5392step0 := by
      have heq : raw5392step0 = (fun i j => raw5392 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5392 permutation34 permutation9
    _ = injectiveMoment H node2366 := by rfl

def raw5393 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical5393 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5393 = injectiveMoment H node2367 := by
  rfl

def raw5394 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical5394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5394 = injectiveMoment H node2368 := by
  rfl

def raw5395 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![2, -1, 1, -2]]

def raw5395step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, -1, 0, -1], ![0, -3, 2, 1], ![0, 4, -2, -2]]

def raw5395step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 1, -3]]

theorem canonical5395 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5395 = injectiveMoment H node576 := by
  calc
    injectiveMoment H raw5395 = injectiveMoment H raw5395step0 := by
      have heq : raw5395step0 = raw5395.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5395).symm
    injectiveMoment H raw5395step0 = injectiveMoment H raw5395step1 := by
      have heq : raw5395step1 = (fun i j => raw5395step0 (permutation27 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5395step0 permutation27 permutation22
    _ = injectiveMoment H node576 := by rfl

def raw5396 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5396step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -3, 0, 3], ![0, 4, 0, -4]]

def raw5396step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -3, 3], ![0, 0, 4, -4], ![1, -2, 0, 1]]

theorem canonical5396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5396 = injectiveMoment H node1373 := by
  calc
    injectiveMoment H raw5396 = injectiveMoment H raw5396step0 := by
      have heq : raw5396step0 = raw5396.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5396).symm
    injectiveMoment H raw5396step0 = injectiveMoment H raw5396step1 := by
      have heq : raw5396step1 = (fun i j => raw5396step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5396step0 permutation18 permutation21
    _ = injectiveMoment H node1373 := by rfl

def raw5397 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw5397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -3, 1, 2], ![0, 4, -1, -3]]

def raw5397step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![0, 3, -1, -2], ![0, -4, 1, 3]]

def raw5397step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

theorem canonical5397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5397 = injectiveMoment H node688 := by
  calc
    injectiveMoment H raw5397 = injectiveMoment H raw5397step0 := by
      have heq : raw5397step0 = raw5397.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5397).symm
    injectiveMoment H raw5397step0 = injectiveMoment H raw5397step1 := by
      have heq : raw5397step1 = -raw5397step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5397step0).symm
    injectiveMoment H raw5397step1 = injectiveMoment H raw5397step2 := by
      have heq : raw5397step2 = (fun i j => raw5397step1 (permutation18 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5397step1 permutation18 permutation12
    _ = injectiveMoment H node688 := by rfl

def raw5398 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw5398step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -3, 2, 1], ![0, 4, -2, -2]]

def raw5398step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

theorem canonical5398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5398 = injectiveMoment H node584 := by
  calc
    injectiveMoment H raw5398 = injectiveMoment H raw5398step0 := by
      have heq : raw5398step0 = raw5398.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5398).symm
    injectiveMoment H raw5398step0 = injectiveMoment H raw5398step1 := by
      have heq : raw5398step1 = (fun i j => raw5398step0 (permutation29 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5398step0 permutation29 permutation28
    _ = injectiveMoment H node584 := by rfl

def raw5399 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw5399step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -3, 3, 0], ![0, 4, -3, -1]]

def raw5399step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, 1, 0]]

theorem canonical5399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5399 = injectiveMoment H node1183 := by
  calc
    injectiveMoment H raw5399 = injectiveMoment H raw5399step0 := by
      have heq : raw5399step0 = raw5399.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5399).symm
    injectiveMoment H raw5399step0 = injectiveMoment H raw5399step1 := by
      have heq : raw5399step1 = (fun i j => raw5399step0 (permutation32 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5399step0 permutation32 permutation28
    _ = injectiveMoment H node1183 := by rfl

def raw5400 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, 0, 2, -3], ![1, -1, 1, -1]]

def raw5400step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, 0, -1], ![0, -3, 2, 1], ![0, 4, -3, -1]]

def raw5400step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 0, 1], ![0, 3, -2, -1], ![0, -4, 3, 1]]

def raw5400step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

theorem canonical5400 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5400 = injectiveMoment H node688 := by
  calc
    injectiveMoment H raw5400 = injectiveMoment H raw5400step0 := by
      have heq : raw5400step0 = raw5400.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5400).symm
    injectiveMoment H raw5400step0 = injectiveMoment H raw5400step1 := by
      have heq : raw5400step1 = -raw5400step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5400step0).symm
    injectiveMoment H raw5400step1 = injectiveMoment H raw5400step2 := by
      have heq : raw5400step2 = (fun i j => raw5400step1 (permutation18 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5400step1 permutation18 permutation14
    _ = injectiveMoment H node688 := by rfl

def raw5401 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5401step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical5401 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5401 = injectiveMoment H node1642 := by
  calc
    injectiveMoment H raw5401 = injectiveMoment H raw5401step0 := by
      have heq : raw5401step0 = (fun i j => raw5401 (permutation68 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5401 permutation68 permutation23
    _ = injectiveMoment H node1642 := by rfl

def raw5402 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5402step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical5402 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5402 = injectiveMoment H node1688 := by
  calc
    injectiveMoment H raw5402 = injectiveMoment H raw5402step0 := by
      have heq : raw5402step0 = (fun i j => raw5402 (permutation75 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5402 permutation75 permutation23
    _ = injectiveMoment H node1688 := by rfl

def raw5403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -2, 0, 2], ![0, 3, 0, -3]]

def raw5403step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

theorem canonical5403 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5403 = injectiveMoment H node1374 := by
  calc
    injectiveMoment H raw5403 = injectiveMoment H raw5403step0 := by
      have heq : raw5403step0 = raw5403.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5403).symm
    injectiveMoment H raw5403step0 = injectiveMoment H raw5403step1 := by
      have heq : raw5403step1 = (fun i j => raw5403step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5403step0 permutation18 permutation21
    _ = injectiveMoment H node1374 := by rfl

def raw5404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5404step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -2, 1, 1], ![0, 3, -1, -2]]

def raw5404step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical5404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5404 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw5404 = injectiveMoment H raw5404step0 := by
      have heq : raw5404step0 = raw5404.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5404).symm
    injectiveMoment H raw5404step0 = injectiveMoment H raw5404step1 := by
      have heq : raw5404step1 = (fun i j => raw5404step0 (permutation29 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5404step0 permutation29 permutation31
    _ = injectiveMoment H node476 := by rfl

def raw5405 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw5405step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -2, 2, 0], ![0, 3, -2, -1]]

def raw5405step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

theorem canonical5405 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5405 = injectiveMoment H node1223 := by
  calc
    injectiveMoment H raw5405 = injectiveMoment H raw5405step0 := by
      have heq : raw5405step0 = raw5405.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5405).symm
    injectiveMoment H raw5405step0 = injectiveMoment H raw5405step1 := by
      have heq : raw5405step1 = (fun i j => raw5405step0 (permutation32 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5405step0 permutation32 permutation28
    _ = injectiveMoment H node1223 := by rfl

def raw5406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw5406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -2, 3, -1], ![0, 3, -3, 0]]

def raw5406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, 0, 1]]

theorem canonical5406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5406 = injectiveMoment H node1226 := by
  calc
    injectiveMoment H raw5406 = injectiveMoment H raw5406step0 := by
      have heq : raw5406step0 = raw5406.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5406).symm
    injectiveMoment H raw5406step0 = injectiveMoment H raw5406step1 := by
      have heq : raw5406step1 = (fun i j => raw5406step0 (permutation26 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5406step0 permutation26 permutation27
    _ = injectiveMoment H node1226 := by rfl

def raw5407 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical5407 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5407 = injectiveMoment H node2369 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
