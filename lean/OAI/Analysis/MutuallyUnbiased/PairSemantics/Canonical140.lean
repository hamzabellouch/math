import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical4480 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4480 = injectiveMoment H node2211 := by
  rfl

def raw4481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4481step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical4481 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4481 = injectiveMoment H node1631 := by
  calc
    injectiveMoment H raw4481 = injectiveMoment H raw4481step0 := by
      have heq : raw4481step0 = (fun i j => raw4481 (permutation73 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4481 permutation73 permutation29
    _ = injectiveMoment H node1631 := by rfl

def raw4482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical4482 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4482 = injectiveMoment H node2212 := by
  rfl

def raw4483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical4483 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4483 = injectiveMoment H node2213 := by
  rfl

def raw4484 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical4484 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4484 = injectiveMoment H node680 := by
  rfl

def raw4485 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 3, 0, -2], ![2, -2, 0, 0]]

def raw4485step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![1, -3, 0, 2], ![-2, 2, 0, 0]]

def raw4485step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical4485 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4485 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw4485 = injectiveMoment H raw4485step0 := by
      have heq : raw4485step0 = raw4485.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4485).symm
    injectiveMoment H raw4485step0 = injectiveMoment H raw4485step1 := by
      have heq : raw4485step1 = -raw4485step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4485step0).symm
    injectiveMoment H raw4485step1 = injectiveMoment H raw4485step2 := by
      have heq : raw4485step2 = (fun i j => raw4485step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4485step1 permutation14 permutation26
    _ = injectiveMoment H node1056 := by rfl

def raw4486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw4486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw4486step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![1, -3, 2, 0], ![-2, 2, -1, 1]]

def raw4486step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

theorem canonical4486 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4486 = injectiveMoment H node1049 := by
  calc
    injectiveMoment H raw4486 = injectiveMoment H raw4486step0 := by
      have heq : raw4486step0 = raw4486.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4486).symm
    injectiveMoment H raw4486step0 = injectiveMoment H raw4486step1 := by
      have heq : raw4486step1 = -raw4486step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4486step0).symm
    injectiveMoment H raw4486step1 = injectiveMoment H raw4486step2 := by
      have heq : raw4486step2 = (fun i j => raw4486step1 (permutation9 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4486step1 permutation9 permutation32
    _ = injectiveMoment H node1049 := by rfl

def raw4487 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, 3, -1, -1], ![2, -2, 0, 0]]

def raw4487step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

theorem canonical4487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4487 = injectiveMoment H node967 := by
  calc
    injectiveMoment H raw4487 = injectiveMoment H raw4487step0 := by
      have heq : raw4487step0 = raw4487.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4487).symm
    injectiveMoment H raw4487step0 = injectiveMoment H raw4487step1 := by
      have heq : raw4487step1 = (fun i j => raw4487step0 (permutation24 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4487step0 permutation24 permutation25
    _ = injectiveMoment H node967 := by rfl

def raw4488 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw4488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, 3, 0, -2], ![2, -2, -1, 1]]

def raw4488step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![1, -3, 0, 2], ![-2, 2, 1, -1]]

def raw4488step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

theorem canonical4488 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4488 = injectiveMoment H node1049 := by
  calc
    injectiveMoment H raw4488 = injectiveMoment H raw4488step0 := by
      have heq : raw4488step0 = raw4488.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4488).symm
    injectiveMoment H raw4488step0 = injectiveMoment H raw4488step1 := by
      have heq : raw4488step1 = -raw4488step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4488step0).symm
    injectiveMoment H raw4488step1 = injectiveMoment H raw4488step2 := by
      have heq : raw4488step2 = (fun i j => raw4488step1 (permutation9 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4488step1 permutation9 permutation26
    _ = injectiveMoment H node1049 := by rfl

def raw4489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical4489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4489 = injectiveMoment H node2214 := by
  rfl

def raw4490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4490step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

theorem canonical4490 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4490 = injectiveMoment H node2852 := by
  calc
    injectiveMoment H raw4490 = injectiveMoment H raw4490step0 := by
      have heq : raw4490step0 = (fun i j => raw4490 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4490 permutation113 permutation15
    _ = injectiveMoment H node2852 := by rfl

def raw4491 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw4491step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

theorem canonical4491 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4491 = injectiveMoment H node2852 := by
  calc
    injectiveMoment H raw4491 = injectiveMoment H raw4491step0 := by
      have heq : raw4491step0 = (fun i j => raw4491 (permutation136 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4491 permutation136 permutation15
    _ = injectiveMoment H node2852 := by rfl

def raw4492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical4492 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4492 = injectiveMoment H node2215 := by
  rfl

def raw4493 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical4493 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4493 = injectiveMoment H node2216 := by
  rfl

def raw4494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw4494step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -2, 0, 3], ![2, 2, -1, -3]]

def raw4494step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 2, 0, -3], ![-2, -2, 1, 3]]

def raw4494step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, -2, -2, 3]]

theorem canonical4494 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4494 = injectiveMoment H node1266 := by
  calc
    injectiveMoment H raw4494 = injectiveMoment H raw4494step0 := by
      have heq : raw4494step0 = raw4494.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4494).symm
    injectiveMoment H raw4494step0 = injectiveMoment H raw4494step1 := by
      have heq : raw4494step1 = -raw4494step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4494step0).symm
    injectiveMoment H raw4494step1 = injectiveMoment H raw4494step2 := by
      have heq : raw4494step2 = (fun i j => raw4494step1 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4494step1 permutation15 permutation23
    _ = injectiveMoment H node1266 := by rfl

def raw4495 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical4495 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4495 = injectiveMoment H node2217 := by
  rfl

def raw4496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical4496 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4496 = injectiveMoment H node681 := by
  rfl

def raw4497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical4497 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4497 = injectiveMoment H node2218 := by
  rfl

def raw4498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -2, 3, 0], ![2, 2, -4, 0]]

def raw4498step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 2, -3, 0], ![-2, -2, 4, 0]]

def raw4498step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 1, -3]]

theorem canonical4498 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4498 = injectiveMoment H node576 := by
  calc
    injectiveMoment H raw4498 = injectiveMoment H raw4498step0 := by
      have heq : raw4498step0 = raw4498.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4498).symm
    injectiveMoment H raw4498step0 = injectiveMoment H raw4498step1 := by
      have heq : raw4498step1 = -raw4498step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4498step0).symm
    injectiveMoment H raw4498step1 = injectiveMoment H raw4498step2 := by
      have heq : raw4498step2 = (fun i j => raw4498step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4498step1 permutation27 permutation19
    _ = injectiveMoment H node576 := by rfl

def raw4499 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4499step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -2, 1, 2], ![2, 2, 0, -4]]

def raw4499step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![1, 2, -1, -2], ![-2, -2, 0, 4]]

def raw4499step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

theorem canonical4499 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4499 = injectiveMoment H node579 := by
  calc
    injectiveMoment H raw4499 = injectiveMoment H raw4499step0 := by
      have heq : raw4499step0 = raw4499.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4499).symm
    injectiveMoment H raw4499step0 = injectiveMoment H raw4499step1 := by
      have heq : raw4499step1 = -raw4499step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4499step0).symm
    injectiveMoment H raw4499step1 = injectiveMoment H raw4499step2 := by
      have heq : raw4499step2 = (fun i j => raw4499step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4499step1 permutation27 permutation17
    _ = injectiveMoment H node579 := by rfl

def raw4500 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

theorem canonical4500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4500 = injectiveMoment H node682 := by
  rfl

def raw4501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw4501step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -2, 3, 0], ![2, 2, -2, -2]]

def raw4501step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical4501 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4501 = injectiveMoment H node593 := by
  calc
    injectiveMoment H raw4501 = injectiveMoment H raw4501step0 := by
      have heq : raw4501step0 = raw4501.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4501).symm
    injectiveMoment H raw4501step0 = injectiveMoment H raw4501step1 := by
      have heq : raw4501step1 = (fun i j => raw4501step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4501step0 permutation21 permutation19
    _ = injectiveMoment H node593 := by rfl

def raw4502 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4502step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -2, 0, 3], ![2, 2, 0, -4]]

def raw4502step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical4502 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4502 = injectiveMoment H node1295 := by
  calc
    injectiveMoment H raw4502 = injectiveMoment H raw4502step0 := by
      have heq : raw4502step0 = raw4502.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4502).symm
    injectiveMoment H raw4502step0 = injectiveMoment H raw4502step1 := by
      have heq : raw4502step1 = (fun i j => raw4502step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4502step0 permutation18 permutation23
    _ = injectiveMoment H node1295 := by rfl

def raw4503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw4503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2]]

theorem canonical4503 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4503 = injectiveMoment H node1370 := by
  calc
    injectiveMoment H raw4503 = injectiveMoment H raw4503step0 := by
      have heq : raw4503step0 = (fun i j => raw4503 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4503 permutation24 permutation15
    _ = injectiveMoment H node1370 := by rfl

def raw4504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw4504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -2, 3, 0], ![2, 2, -3, -1]]

def raw4504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, 2, -3, 0], ![-2, -2, 3, 1]]

def raw4504step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

theorem canonical4504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4504 = injectiveMoment H node1317 := by
  calc
    injectiveMoment H raw4504 = injectiveMoment H raw4504step0 := by
      have heq : raw4504step0 = raw4504.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4504).symm
    injectiveMoment H raw4504step0 = injectiveMoment H raw4504step1 := by
      have heq : raw4504step1 = -raw4504step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4504step0).symm
    injectiveMoment H raw4504step1 = injectiveMoment H raw4504step2 := by
      have heq : raw4504step2 = (fun i j => raw4504step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4504step1 permutation9 permutation29
    _ = injectiveMoment H node1317 := by rfl

def raw4505 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw4505step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-1, -2, 3, 0], ![2, 2, -4, 0]]

def raw4505step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical4505 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4505 = injectiveMoment H node1295 := by
  calc
    injectiveMoment H raw4505 = injectiveMoment H raw4505step0 := by
      have heq : raw4505step0 = raw4505.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4505).symm
    injectiveMoment H raw4505step0 = injectiveMoment H raw4505step1 := by
      have heq : raw4505step1 = (fun i j => raw4505step0 (permutation18 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4505step0 permutation18 permutation29
    _ = injectiveMoment H node1295 := by rfl

def raw4506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, 1, 1, -3], ![1, -2, 2, -1]]

def raw4506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

theorem canonical4506 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4506 = injectiveMoment H node682 := by
  calc
    injectiveMoment H raw4506 = injectiveMoment H raw4506step0 := by
      have heq : raw4506step0 = (fun i j => raw4506 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4506 permutation10 permutation9
    _ = injectiveMoment H node682 := by rfl

def raw4507 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4507step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw4507step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

theorem canonical4507 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4507 = injectiveMoment H node1552 := by
  calc
    injectiveMoment H raw4507 = injectiveMoment H raw4507step0 := by
      have heq : raw4507step0 = -raw4507 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4507).symm
    injectiveMoment H raw4507step0 = injectiveMoment H raw4507step1 := by
      have heq : raw4507step1 = (fun i j => raw4507step0 (permutation150 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4507step0 permutation150 permutation21
    _ = injectiveMoment H node1552 := by rfl

def raw4508 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4508step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical4508 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4508 = injectiveMoment H node1736 := by
  calc
    injectiveMoment H raw4508 = injectiveMoment H raw4508step0 := by
      have heq : raw4508step0 = (fun i j => raw4508 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4508 permutation33 permutation11
    _ = injectiveMoment H node1736 := by rfl

def raw4509 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4509step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical4509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4509 = injectiveMoment H node2207 := by
  calc
    injectiveMoment H raw4509 = injectiveMoment H raw4509step0 := by
      have heq : raw4509step0 = (fun i j => raw4509 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4509 permutation39 permutation9
    _ = injectiveMoment H node2207 := by rfl

def raw4510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4510step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical4510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4510 = injectiveMoment H node2209 := by
  calc
    injectiveMoment H raw4510 = injectiveMoment H raw4510step0 := by
      have heq : raw4510step0 = (fun i j => raw4510 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4510 permutation39 permutation9
    _ = injectiveMoment H node2209 := by rfl

def raw4511 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical4511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4511 = injectiveMoment H node2219 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
