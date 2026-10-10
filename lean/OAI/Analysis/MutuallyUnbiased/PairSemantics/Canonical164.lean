import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5248 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5248step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical5248 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5248 = injectiveMoment H node1520 := by
  calc
    injectiveMoment H raw5248 = injectiveMoment H raw5248step0 := by
      have heq : raw5248step0 = (fun i j => raw5248 (permutation35 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5248 permutation35 permutation21
    _ = injectiveMoment H node1520 := by rfl

def raw5249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 0, 0, 2], ![2, 1, 0, -3]]

def raw5249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

theorem canonical5249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5249 = injectiveMoment H node1052 := by
  calc
    injectiveMoment H raw5249 = injectiveMoment H raw5249step0 := by
      have heq : raw5249step0 = raw5249.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5249).symm
    injectiveMoment H raw5249step0 = injectiveMoment H raw5249step1 := by
      have heq : raw5249step1 = (fun i j => raw5249step0 (permutation18 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5249step0 permutation18 permutation24
    _ = injectiveMoment H node1052 := by rfl

def raw5250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 0, 1, 1], ![2, 1, -1, -2]]

def raw5250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical5250 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5250 = injectiveMoment H node1084 := by
  calc
    injectiveMoment H raw5250 = injectiveMoment H raw5250step0 := by
      have heq : raw5250step0 = raw5250.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5250).symm
    injectiveMoment H raw5250step0 = injectiveMoment H raw5250step1 := by
      have heq : raw5250step1 = (fun i j => raw5250step0 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5250step0 permutation15 permutation18
    _ = injectiveMoment H node1084 := by rfl

def raw5251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw5251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 0, 2, 0], ![2, 1, -2, -1]]

def raw5251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, 0, -2, 0], ![-2, -1, 2, 1]]

def raw5251step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical5251 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5251 = injectiveMoment H node1253 := by
  calc
    injectiveMoment H raw5251 = injectiveMoment H raw5251step0 := by
      have heq : raw5251step0 = raw5251.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5251).symm
    injectiveMoment H raw5251step0 = injectiveMoment H raw5251step1 := by
      have heq : raw5251step1 = -raw5251step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5251step0).symm
    injectiveMoment H raw5251step1 = injectiveMoment H raw5251step2 := by
      have heq : raw5251step2 = (fun i j => raw5251step1 (permutation11 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5251step1 permutation11 permutation30
    _ = injectiveMoment H node1253 := by rfl

def raw5252 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5252step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical5252 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5252 = injectiveMoment H node1520 := by
  calc
    injectiveMoment H raw5252 = injectiveMoment H raw5252step0 := by
      have heq : raw5252step0 = (fun i j => raw5252 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5252 permutation39 permutation11
    _ = injectiveMoment H node1520 := by rfl

def raw5253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical5253 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5253 = injectiveMoment H node2337 := by
  rfl

def raw5254 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw5254step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical5254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5254 = injectiveMoment H node2338 := by
  calc
    injectiveMoment H raw5254 = injectiveMoment H raw5254step0 := by
      have heq : raw5254step0 = (fun i j => raw5254 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5254 permutation34 permutation9
    _ = injectiveMoment H node2338 := by rfl

def raw5255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 0, -2]]

def raw5255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical5255 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5255 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw5255 = injectiveMoment H raw5255step0 := by
      have heq : raw5255step0 = raw5255.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5255).symm
    injectiveMoment H raw5255step0 = injectiveMoment H raw5255step1 := by
      have heq : raw5255step1 = (fun i j => raw5255step0 (permutation19 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5255step0 permutation19 permutation18
    _ = injectiveMoment H node1033 := by rfl

def raw5256 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw5256step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 2, -1, 1], ![2, -1, 1, -2]]

def raw5256step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]

theorem canonical5256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5256 = injectiveMoment H node500 := by
  calc
    injectiveMoment H raw5256 = injectiveMoment H raw5256step0 := by
      have heq : raw5256step0 = raw5256.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5256).symm
    injectiveMoment H raw5256step0 = injectiveMoment H raw5256step1 := by
      have heq : raw5256step1 = (fun i j => raw5256step0 (permutation29 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5256step0 permutation29 permutation30
    _ = injectiveMoment H node500 := by rfl

def raw5257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5257step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 2, 0, 0], ![2, -1, 0, -1]]

def raw5257step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -2, 0, 0], ![-2, 1, 0, 1]]

def raw5257step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical5257 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5257 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw5257 = injectiveMoment H raw5257step0 := by
      have heq : raw5257step0 = raw5257.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5257).symm
    injectiveMoment H raw5257step0 = injectiveMoment H raw5257step1 := by
      have heq : raw5257step1 = -raw5257step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5257step0).symm
    injectiveMoment H raw5257step1 = injectiveMoment H raw5257step2 := by
      have heq : raw5257step2 = (fun i j => raw5257step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5257step1 permutation12 permutation26
    _ = injectiveMoment H node1033 := by rfl

def raw5258 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw5258step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1], ![2, -1, -1, 0]]

def raw5258step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1], ![-2, 1, 1, 0]]

def raw5258step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical5258 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5258 = injectiveMoment H node1084 := by
  calc
    injectiveMoment H raw5258 = injectiveMoment H raw5258step0 := by
      have heq : raw5258step0 = raw5258.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5258).symm
    injectiveMoment H raw5258step0 = injectiveMoment H raw5258step1 := by
      have heq : raw5258step1 = -raw5258step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5258step0).symm
    injectiveMoment H raw5258step1 = injectiveMoment H raw5258step2 := by
      have heq : raw5258step2 = (fun i j => raw5258step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5258step1 permutation10 permutation32
    _ = injectiveMoment H node1084 := by rfl

def raw5259 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5259step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 3, -1, 0], ![2, -2, 1, -1]]

def raw5259step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -3, 1, 0], ![-2, 2, -1, 1]]

def raw5259step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical5259 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5259 = injectiveMoment H node1073 := by
  calc
    injectiveMoment H raw5259 = injectiveMoment H raw5259step0 := by
      have heq : raw5259step0 = raw5259.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5259).symm
    injectiveMoment H raw5259step0 = injectiveMoment H raw5259step1 := by
      have heq : raw5259step1 = -raw5259step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5259step0).symm
    injectiveMoment H raw5259step1 = injectiveMoment H raw5259step2 := by
      have heq : raw5259step2 = (fun i j => raw5259step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5259step1 permutation11 permutation32
    _ = injectiveMoment H node1073 := by rfl

def raw5260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw5260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 3, 0, -1], ![2, -2, 0, 0]]

def raw5260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -3, 0, 1], ![-2, 2, 0, 0]]

def raw5260step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

theorem canonical5260 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5260 = injectiveMoment H node1052 := by
  calc
    injectiveMoment H raw5260 = injectiveMoment H raw5260step0 := by
      have heq : raw5260step0 = raw5260.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5260).symm
    injectiveMoment H raw5260step0 = injectiveMoment H raw5260step1 := by
      have heq : raw5260step1 = -raw5260step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5260step0).symm
    injectiveMoment H raw5260step1 = injectiveMoment H raw5260step2 := by
      have heq : raw5260step2 = (fun i j => raw5260step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5260step1 permutation14 permutation26
    _ = injectiveMoment H node1052 := by rfl

def raw5261 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5261step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical5261 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5261 = injectiveMoment H node2336 := by
  calc
    injectiveMoment H raw5261 = injectiveMoment H raw5261step0 := by
      have heq : raw5261step0 = (fun i j => raw5261 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5261 permutation39 permutation9
    _ = injectiveMoment H node2336 := by rfl

def raw5262 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5262step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical5262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5262 = injectiveMoment H node2337 := by
  calc
    injectiveMoment H raw5262 = injectiveMoment H raw5262step0 := by
      have heq : raw5262step0 = (fun i j => raw5262 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5262 permutation39 permutation9
    _ = injectiveMoment H node2337 := by rfl

def raw5263 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5263step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical5263 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5263 = injectiveMoment H node2339 := by
  calc
    injectiveMoment H raw5263 = injectiveMoment H raw5263step0 := by
      have heq : raw5263step0 = (fun i j => raw5263 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5263 permutation39 permutation9
    _ = injectiveMoment H node2339 := by rfl

def raw5264 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

theorem canonical5264 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5264 = injectiveMoment H node2340 := by
  rfl

def raw5265 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

theorem canonical5265 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5265 = injectiveMoment H node2341 := by
  rfl

def raw5266 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw5266step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

theorem canonical5266 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5266 = injectiveMoment H node2280 := by
  calc
    injectiveMoment H raw5266 = injectiveMoment H raw5266step0 := by
      have heq : raw5266step0 = (fun i j => raw5266 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5266 permutation113 permutation15
    _ = injectiveMoment H node2280 := by rfl

def raw5267 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw5267step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

theorem canonical5267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5267 = injectiveMoment H node2279 := by
  calc
    injectiveMoment H raw5267 = injectiveMoment H raw5267step0 := by
      have heq : raw5267step0 = (fun i j => raw5267 (permutation119 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5267 permutation119 permutation16
    _ = injectiveMoment H node2279 := by rfl

def raw5268 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical5268 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5268 = injectiveMoment H node2342 := by
  rfl

def raw5269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical5269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5269 = injectiveMoment H node2343 := by
  rfl

def raw5270 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 0, 1, -2]]

def raw5270step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -2, 2]]

theorem canonical5270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5270 = injectiveMoment H node2282 := by
  calc
    injectiveMoment H raw5270 = injectiveMoment H raw5270step0 := by
      have heq : raw5270step0 = (fun i j => raw5270 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5270 permutation113 permutation15
    _ = injectiveMoment H node2282 := by rfl

def raw5271 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical5271 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5271 = injectiveMoment H node2344 := by
  rfl

def raw5272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw5272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw5272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw5272step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical5272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5272 = injectiveMoment H node1319 := by
  calc
    injectiveMoment H raw5272 = injectiveMoment H raw5272step0 := by
      have heq : raw5272step0 = raw5272.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5272).symm
    injectiveMoment H raw5272step0 = injectiveMoment H raw5272step1 := by
      have heq : raw5272step1 = -raw5272step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5272step0).symm
    injectiveMoment H raw5272step1 = injectiveMoment H raw5272step2 := by
      have heq : raw5272step2 = (fun i j => raw5272step1 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5272step1 permutation27 permutation18
    _ = injectiveMoment H node1319 := by rfl

def raw5273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw5273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, -1, 2, 1], ![2, 1, -1, -2]]

def raw5273step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2]]

theorem canonical5273 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5273 = injectiveMoment H node1370 := by
  calc
    injectiveMoment H raw5273 = injectiveMoment H raw5273step0 := by
      have heq : raw5273step0 = raw5273.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5273).symm
    injectiveMoment H raw5273step0 = injectiveMoment H raw5273step1 := by
      have heq : raw5273step1 = (fun i j => raw5273step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5273step0 permutation23 permutation20
    _ = injectiveMoment H node1370 := by rfl

def raw5274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw5274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, -1, 3, 0], ![2, 1, -2, -1]]

def raw5274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 2, -2]]

theorem canonical5274 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5274 = injectiveMoment H node1219 := by
  calc
    injectiveMoment H raw5274 = injectiveMoment H raw5274step0 := by
      have heq : raw5274step0 = raw5274.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5274).symm
    injectiveMoment H raw5274step0 = injectiveMoment H raw5274step1 := by
      have heq : raw5274step1 = (fun i j => raw5274step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5274step0 permutation23 permutation19
    _ = injectiveMoment H node1219 := by rfl

def raw5275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw5275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical5275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5275 = injectiveMoment H node1205 := by
  calc
    injectiveMoment H raw5275 = injectiveMoment H raw5275step0 := by
      have heq : raw5275step0 = raw5275.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5275).symm
    injectiveMoment H raw5275step0 = injectiveMoment H raw5275step1 := by
      have heq : raw5275step1 = (fun i j => raw5275step0 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5275step0 permutation23 permutation17
    _ = injectiveMoment H node1205 := by rfl

def raw5276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, -1, 1, 2], ![2, 1, -1, -2]]

def raw5276step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical5276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5276 = injectiveMoment H node1368 := by
  calc
    injectiveMoment H raw5276 = injectiveMoment H raw5276step0 := by
      have heq : raw5276step0 = raw5276.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5276).symm
    injectiveMoment H raw5276step0 = injectiveMoment H raw5276step1 := by
      have heq : raw5276step1 = (fun i j => raw5276step0 (permutation23 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5276step0 permutation23 permutation18
    _ = injectiveMoment H node1368 := by rfl

def raw5277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw5277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, -1, 2, 1], ![2, 1, -2, -1]]

def raw5277step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical5277 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5277 = injectiveMoment H node1368 := by
  calc
    injectiveMoment H raw5277 = injectiveMoment H raw5277step0 := by
      have heq : raw5277step0 = raw5277.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5277).symm
    injectiveMoment H raw5277step0 = injectiveMoment H raw5277step1 := by
      have heq : raw5277step1 = (fun i j => raw5277step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5277step0 permutation23 permutation20
    _ = injectiveMoment H node1368 := by rfl

def raw5278 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5278step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-2, 0, 1, 0, 1], ![2, 0, -1, 0, -1]]

def raw5278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw5278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical5278 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5278 = injectiveMoment H node1237 := by
  calc
    injectiveMoment H raw5278 = injectiveMoment H raw5278step0 := by
      have heq : raw5278step0 = raw5278.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5278).symm
    injectiveMoment H raw5278step0 = injectiveMoment H raw5278step1 := by
      have hz : ∀ i, raw5278step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw5278step1 = (fun i j => raw5278step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5278step0 permutation57 hz
    injectiveMoment H raw5278step1 = injectiveMoment H raw5278step2 := by
      have heq : raw5278step2 = (fun i j => raw5278step1 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5278step1 permutation29 permutation18
    _ = injectiveMoment H node1237 := by rfl

def raw5279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 0, 1, 1], ![2, 0, -1, -1]]

def raw5279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2], ![-2, 1, 1], ![2, -1, -1]]

def raw5279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5279 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw5279 = injectiveMoment H raw5279step0 := by
      have heq : raw5279step0 = raw5279.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5279).symm
    injectiveMoment H raw5279step0 = injectiveMoment H raw5279step1 := by
      have hz : ∀ i, raw5279step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5279step1 = (fun i j => raw5279step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5279step0 permutation15 hz
    injectiveMoment H raw5279step1 = injectiveMoment H raw5279step2 := by
      have heq : raw5279step2 = (fun i j => raw5279step1 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5279step1 permutation29 permutation6
    _ = injectiveMoment H node279 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
