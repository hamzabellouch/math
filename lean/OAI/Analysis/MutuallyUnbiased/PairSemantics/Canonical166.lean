import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5312 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5312step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -2, 1, -1], ![0, 1, -3, 2], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw5312step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical5312 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5312 = injectiveMoment H node2350 := by
  calc
    injectiveMoment H raw5312 = injectiveMoment H raw5312step0 := by
      have heq : raw5312step0 = -raw5312 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5312).symm
    injectiveMoment H raw5312step0 = injectiveMoment H raw5312step1 := by
      have heq : raw5312step1 = (fun i j => raw5312step0 (permutation54 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5312step0 permutation54 permutation16
    _ = injectiveMoment H node2350 := by rfl

def raw5313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw5313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, 3, -2, 0], ![1, -2, 2, -1]]

def raw5313step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

theorem canonical5313 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5313 = injectiveMoment H node824 := by
  calc
    injectiveMoment H raw5313 = injectiveMoment H raw5313step0 := by
      have heq : raw5313step0 = raw5313.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5313).symm
    injectiveMoment H raw5313step0 = injectiveMoment H raw5313step1 := by
      have heq : raw5313step1 = (fun i j => raw5313step0 (permutation30 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5313step0 permutation30 permutation29
    _ = injectiveMoment H node824 := by rfl

def raw5314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw5314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, 3, -1, -1], ![1, -2, 1, 0]]

def raw5314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical5314 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5314 = injectiveMoment H node943 := by
  calc
    injectiveMoment H raw5314 = injectiveMoment H raw5314step0 := by
      have heq : raw5314step0 = raw5314.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5314).symm
    injectiveMoment H raw5314step0 = injectiveMoment H raw5314step1 := by
      have heq : raw5314step1 = (fun i j => raw5314step0 (permutation24 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5314step0 permutation24 permutation31
    _ = injectiveMoment H node943 := by rfl

def raw5315 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw5315step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, 3, 0, -2], ![1, -2, 0, 1]]

def raw5315step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![1, -3, 0, 2], ![-1, 2, 0, -1]]

def raw5315step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical5315 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5315 = injectiveMoment H node1007 := by
  calc
    injectiveMoment H raw5315 = injectiveMoment H raw5315step0 := by
      have heq : raw5315step0 = raw5315.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5315).symm
    injectiveMoment H raw5315step0 = injectiveMoment H raw5315step1 := by
      have heq : raw5315step1 = -raw5315step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5315step0).symm
    injectiveMoment H raw5315step1 = injectiveMoment H raw5315step2 := by
      have heq : raw5315step2 = (fun i j => raw5315step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5315step1 permutation14 permutation26
    _ = injectiveMoment H node1007 := by rfl

def raw5316 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

theorem canonical5316 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5316 = injectiveMoment H node2351 := by
  rfl

def raw5317 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

theorem canonical5317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5317 = injectiveMoment H node2352 := by
  rfl

def raw5318 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical5318 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5318 = injectiveMoment H node2353 := by
  rfl

def raw5319 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical5319 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5319 = injectiveMoment H node2354 := by
  rfl

def raw5320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![2, -2, 2, -2]]

def raw5320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -2, 1, 2], ![1, 2, -1, -2]]

def raw5320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -2, -1, 2]]

theorem canonical5320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5320 = injectiveMoment H node1377 := by
  calc
    injectiveMoment H raw5320 = injectiveMoment H raw5320step0 := by
      have heq : raw5320step0 = raw5320.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5320).symm
    injectiveMoment H raw5320step0 = injectiveMoment H raw5320step1 := by
      have heq : raw5320step1 = (fun i j => raw5320step0 (permutation27 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5320step0 permutation27 permutation23
    _ = injectiveMoment H node1377 := by rfl

def raw5321 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical5321 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5321 = injectiveMoment H node2355 := by
  rfl

def raw5322 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw5322step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical5322 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5322 = injectiveMoment H node2355 := by
  calc
    injectiveMoment H raw5322 = injectiveMoment H raw5322step0 := by
      have heq : raw5322step0 = (fun i j => raw5322 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5322 permutation34 permutation9
    _ = injectiveMoment H node2355 := by rfl

def raw5323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 1, -1]]

theorem canonical5323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5323 = injectiveMoment H node719 := by
  rfl

def raw5324 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical5324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5324 = injectiveMoment H node2356 := by
  rfl

def raw5325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![2, -2, 0, 0]]

def raw5325step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -2, 3, 0], ![1, 2, -3, 0]]

def raw5325step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 1, -3]]

theorem canonical5325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5325 = injectiveMoment H node587 := by
  calc
    injectiveMoment H raw5325 = injectiveMoment H raw5325step0 := by
      have heq : raw5325step0 = raw5325.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5325).symm
    injectiveMoment H raw5325step0 = injectiveMoment H raw5325step1 := by
      have heq : raw5325step1 = (fun i j => raw5325step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5325step0 permutation23 permutation19
    _ = injectiveMoment H node587 := by rfl

def raw5326 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw5326step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-1, -2, 0, 3], ![1, 2, 1, -4]]

def raw5326step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![1, 2, 0, -3], ![-1, -2, -1, 4]]

def raw5326step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

theorem canonical5326 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5326 = injectiveMoment H node448 := by
  calc
    injectiveMoment H raw5326 = injectiveMoment H raw5326step0 := by
      have heq : raw5326step0 = raw5326.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5326).symm
    injectiveMoment H raw5326step0 = injectiveMoment H raw5326step1 := by
      have heq : raw5326step1 = -raw5326step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5326step0).symm
    injectiveMoment H raw5326step1 = injectiveMoment H raw5326step2 := by
      have heq : raw5326step2 = (fun i j => raw5326step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5326step1 permutation27 permutation17
    _ = injectiveMoment H node448 := by rfl

def raw5327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw5327step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-1, -2, 1, 2], ![1, 2, 0, -3]]

def raw5327step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![1, 2, -1, -2], ![-1, -2, 0, 3]]

def raw5327step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem canonical5327 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5327 = injectiveMoment H node588 := by
  calc
    injectiveMoment H raw5327 = injectiveMoment H raw5327step0 := by
      have heq : raw5327step0 = raw5327.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5327).symm
    injectiveMoment H raw5327step0 = injectiveMoment H raw5327step1 := by
      have heq : raw5327step1 = -raw5327step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5327step0).symm
    injectiveMoment H raw5327step1 = injectiveMoment H raw5327step2 := by
      have heq : raw5327step2 = (fun i j => raw5327step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5327step1 permutation27 permutation17
    _ = injectiveMoment H node588 := by rfl

def raw5328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw5328step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

theorem canonical5328 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5328 = injectiveMoment H node683 := by
  calc
    injectiveMoment H raw5328 = injectiveMoment H raw5328step0 := by
      have heq : raw5328step0 = (fun i j => raw5328 (permutation24 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5328 permutation24 permutation16
    _ = injectiveMoment H node683 := by rfl

def raw5329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw5329step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-1, -2, 3, 0], ![1, 2, -2, -1]]

def raw5329step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![1, 2, -3, 0], ![-1, -2, 2, 1]]

def raw5329step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

theorem canonical5329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5329 = injectiveMoment H node1315 := by
  calc
    injectiveMoment H raw5329 = injectiveMoment H raw5329step0 := by
      have heq : raw5329step0 = raw5329.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5329).symm
    injectiveMoment H raw5329step0 = injectiveMoment H raw5329step1 := by
      have heq : raw5329step1 = -raw5329step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5329step0).symm
    injectiveMoment H raw5329step1 = injectiveMoment H raw5329step2 := by
      have heq : raw5329step2 = (fun i j => raw5329step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5329step1 permutation9 permutation29
    _ = injectiveMoment H node1315 := by rfl

def raw5330 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5330step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -2, 0, 3], ![1, 2, 0, -3]]

def raw5330step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -1, 3], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical5330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5330 = injectiveMoment H node1303 := by
  calc
    injectiveMoment H raw5330 = injectiveMoment H raw5330step0 := by
      have heq : raw5330step0 = raw5330.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5330).symm
    injectiveMoment H raw5330step0 = injectiveMoment H raw5330step1 := by
      have heq : raw5330step1 = (fun i j => raw5330step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5330step0 permutation18 permutation23
    _ = injectiveMoment H node1303 := by rfl

def raw5331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5331step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -2, 1, 2], ![1, 2, -1, -2]]

def raw5331step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, -1, 1, -2]]

theorem canonical5331 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5331 = injectiveMoment H node678 := by
  calc
    injectiveMoment H raw5331 = injectiveMoment H raw5331step0 := by
      have heq : raw5331step0 = raw5331.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5331).symm
    injectiveMoment H raw5331step0 = injectiveMoment H raw5331step1 := by
      have heq : raw5331step1 = (fun i j => raw5331step0 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5331step0 permutation23 permutation17
    _ = injectiveMoment H node678 := by rfl

def raw5332 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw5332step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -2, 2, 1], ![1, 2, -2, -1]]

def raw5332step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, -1, 1, -2]]

theorem canonical5332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5332 = injectiveMoment H node678 := by
  calc
    injectiveMoment H raw5332 = injectiveMoment H raw5332step0 := by
      have heq : raw5332step0 = raw5332.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5332).symm
    injectiveMoment H raw5332step0 = injectiveMoment H raw5332step1 := by
      have heq : raw5332step1 = (fun i j => raw5332step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5332step0 permutation23 permutation19
    _ = injectiveMoment H node678 := by rfl

def raw5333 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, -1, 0, 0]]

def raw5333step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -2, 3, 0], ![1, 2, -3, 0]]

def raw5333step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -1, 3], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical5333 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5333 = injectiveMoment H node1303 := by
  calc
    injectiveMoment H raw5333 = injectiveMoment H raw5333step0 := by
      have heq : raw5333step0 = raw5333.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5333).symm
    injectiveMoment H raw5333step0 = injectiveMoment H raw5333step1 := by
      have heq : raw5333step1 = (fun i j => raw5333step0 (permutation18 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5333step0 permutation18 permutation29
    _ = injectiveMoment H node1303 := by rfl

def raw5334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical5334 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5334 = injectiveMoment H node2348 := by
  calc
    injectiveMoment H raw5334 = injectiveMoment H raw5334step0 := by
      have heq : raw5334step0 = (fun i j => raw5334 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5334 permutation39 permutation9
    _ = injectiveMoment H node2348 := by rfl

def raw5335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw5335step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

theorem canonical5335 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5335 = injectiveMoment H node2278 := by
  calc
    injectiveMoment H raw5335 = injectiveMoment H raw5335step0 := by
      have heq : raw5335step0 = (fun i j => raw5335 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5335 permutation113 permutation15
    _ = injectiveMoment H node2278 := by rfl

def raw5336 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical5336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5336 = injectiveMoment H node2357 := by
  rfl

def raw5337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5337step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, -1, 0, 1, 1], ![1, 1, 0, -1, -1]]

def raw5337step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 1, 1], ![1, 1, -1, -1]]

def raw5337step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem canonical5337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5337 = injectiveMoment H node1344 := by
  calc
    injectiveMoment H raw5337 = injectiveMoment H raw5337step0 := by
      have heq : raw5337step0 = raw5337.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5337).symm
    injectiveMoment H raw5337step0 = injectiveMoment H raw5337step1 := by
      have hz : ∀ i, raw5337step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw5337step1 = (fun i j => raw5337step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5337step0 permutation80 hz
    injectiveMoment H raw5337step1 = injectiveMoment H raw5337step2 := by
      have heq : raw5337step2 = (fun i j => raw5337step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5337step1 permutation21 permutation17
    _ = injectiveMoment H node1344 := by rfl

def raw5338 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5338step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, -1, 0, 2, 0], ![1, 1, 0, -2, 0]]

def raw5338step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 2, 0], ![1, 1, -2, 0]]

def raw5338step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5338 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw5338 = injectiveMoment H raw5338step0 := by
      have heq : raw5338step0 = raw5338.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5338).symm
    injectiveMoment H raw5338step0 = injectiveMoment H raw5338step1 := by
      have hz : ∀ i, raw5338step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw5338step1 = (fun i j => raw5338step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5338step0 permutation80 hz
    injectiveMoment H raw5338step1 = injectiveMoment H raw5338step2 := by
      have heq : raw5338step2 = (fun i j => raw5338step1 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5338step1 permutation23 permutation20
    _ = injectiveMoment H node1304 := by rfl

def raw5339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5339step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-1, -1, 0, 0, 2], ![1, 1, 0, 0, -2]]

def raw5339step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -1, 0, 2], ![1, 1, 0, -2]]

def raw5339step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical5339 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5339 = injectiveMoment H node1244 := by
  calc
    injectiveMoment H raw5339 = injectiveMoment H raw5339step0 := by
      have heq : raw5339step0 = raw5339.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5339).symm
    injectiveMoment H raw5339step0 = injectiveMoment H raw5339step1 := by
      have hz : ∀ i, raw5339step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw5339step1 = (fun i j => raw5339step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5339step0 permutation80 hz
    injectiveMoment H raw5339step1 = injectiveMoment H raw5339step2 := by
      have heq : raw5339step2 = (fun i j => raw5339step1 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5339step1 permutation23 permutation17
    _ = injectiveMoment H node1244 := by rfl

def raw5340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, -2, 1, -1]]

def raw5340step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, -1, 1, 0, 1], ![1, 1, -1, 0, -1]]

def raw5340step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 1, 1], ![1, 1, -1, -1]]

def raw5340step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem canonical5340 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5340 = injectiveMoment H node1344 := by
  calc
    injectiveMoment H raw5340 = injectiveMoment H raw5340step0 := by
      have heq : raw5340step0 = raw5340.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5340).symm
    injectiveMoment H raw5340step0 = injectiveMoment H raw5340step1 := by
      have hz : ∀ i, raw5340step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw5340step1 = (fun i j => raw5340step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5340step0 permutation104 hz
    injectiveMoment H raw5340step1 = injectiveMoment H raw5340step2 := by
      have heq : raw5340step2 = (fun i j => raw5340step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5340step1 permutation21 permutation17
    _ = injectiveMoment H node1344 := by rfl

def raw5341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0]]

def raw5341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical5341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5341 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw5341 = injectiveMoment H raw5341step0 := by
      have heq : raw5341step0 = (fun i j => raw5341 (permutation33 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5341 permutation33 permutation12
    _ = injectiveMoment H node1746 := by rfl

def raw5342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, -1, 1]]

theorem canonical5342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5342 = injectiveMoment H node2358 := by
  rfl

def raw5343 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem canonical5343 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5343 = injectiveMoment H node2359 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
