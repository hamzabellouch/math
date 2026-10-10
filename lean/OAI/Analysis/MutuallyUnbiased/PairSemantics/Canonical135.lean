import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw4320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 2, -1, 1], ![3, -1, 0, -2]]

def raw4320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -2, 1, -1], ![-3, 1, 0, 2]]

def raw4320step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical4320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4320 = injectiveMoment H node1050 := by
  calc
    injectiveMoment H raw4320 = injectiveMoment H raw4320step0 := by
      have heq : raw4320step0 = raw4320.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4320).symm
    injectiveMoment H raw4320step0 = injectiveMoment H raw4320step1 := by
      have heq : raw4320step1 = -raw4320step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4320step0).symm
    injectiveMoment H raw4320step1 = injectiveMoment H raw4320step2 := by
      have heq : raw4320step2 = (fun i j => raw4320step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4320step1 permutation10 permutation26
    _ = injectiveMoment H node1050 := by rfl

def raw4321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![3, -1, -1, -1]]

def raw4321step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical4321 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4321 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw4321 = injectiveMoment H raw4321step0 := by
      have heq : raw4321step0 = raw4321.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4321).symm
    injectiveMoment H raw4321step0 = injectiveMoment H raw4321step1 := by
      have heq : raw4321step1 = (fun i j => raw4321step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4321step0 permutation30 permutation26
    _ = injectiveMoment H node959 := by rfl

def raw4322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw4322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw4322step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -2, -1, 1], ![-3, 1, 2, 0]]

def raw4322step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical4322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4322 = injectiveMoment H node1050 := by
  calc
    injectiveMoment H raw4322 = injectiveMoment H raw4322step0 := by
      have heq : raw4322step0 = raw4322.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4322).symm
    injectiveMoment H raw4322step0 = injectiveMoment H raw4322step1 := by
      have heq : raw4322step1 = -raw4322step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4322step0).symm
    injectiveMoment H raw4322step1 = injectiveMoment H raw4322step2 := by
      have heq : raw4322step2 = (fun i j => raw4322step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4322step1 permutation10 permutation32
    _ = injectiveMoment H node1050 := by rfl

def raw4323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 1, 1, -3], ![1, -1, -1, 1]]

def raw4323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical4323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4323 = injectiveMoment H node673 := by
  calc
    injectiveMoment H raw4323 = injectiveMoment H raw4323step0 := by
      have heq : raw4323step0 = (fun i j => raw4323 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4323 permutation10 permutation9
    _ = injectiveMoment H node673 := by rfl

def raw4324 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical4324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4324 = injectiveMoment H node2175 := by
  rfl

def raw4325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4325step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 3, -1, 0], ![3, -2, 0, -1]]

def raw4325step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical4325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4325 = injectiveMoment H node1318 := by
  calc
    injectiveMoment H raw4325 = injectiveMoment H raw4325step0 := by
      have heq : raw4325step0 = raw4325.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4325).symm
    injectiveMoment H raw4325step0 = injectiveMoment H raw4325step1 := by
      have heq : raw4325step1 = (fun i j => raw4325step0 (permutation25 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4325step0 permutation25 permutation26
    _ = injectiveMoment H node1318 := by rfl

def raw4326 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical4326 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4326 = injectiveMoment H node2176 := by
  rfl

def raw4327 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical4327 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4327 = injectiveMoment H node2177 := by
  rfl

def raw4328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical4328 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4328 = injectiveMoment H node674 := by
  rfl

def raw4329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4329step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 3, 0, -1], ![3, -2, 0, -1]]

def raw4329step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -3, 0, 1], ![-3, 2, 0, 1]]

def raw4329step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical4329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4329 = injectiveMoment H node1074 := by
  calc
    injectiveMoment H raw4329 = injectiveMoment H raw4329step0 := by
      have heq : raw4329step0 = raw4329.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4329).symm
    injectiveMoment H raw4329step0 = injectiveMoment H raw4329step1 := by
      have heq : raw4329step1 = -raw4329step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4329step0).symm
    injectiveMoment H raw4329step1 = injectiveMoment H raw4329step2 := by
      have heq : raw4329step2 = (fun i j => raw4329step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4329step1 permutation12 permutation26
    _ = injectiveMoment H node1074 := by rfl

def raw4330 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4330step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 3, -1, 0], ![3, -2, 0, -1]]

def raw4330step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -3, 1, 0], ![-3, 2, 0, 1]]

def raw4330step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

theorem canonical4330 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4330 = injectiveMoment H node1046 := by
  calc
    injectiveMoment H raw4330 = injectiveMoment H raw4330step0 := by
      have heq : raw4330step0 = raw4330.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4330).symm
    injectiveMoment H raw4330step0 = injectiveMoment H raw4330step1 := by
      have heq : raw4330step1 = -raw4330step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4330step0).symm
    injectiveMoment H raw4330step1 = injectiveMoment H raw4330step2 := by
      have heq : raw4330step2 = (fun i j => raw4330step1 (permutation9 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4330step1 permutation9 permutation32
    _ = injectiveMoment H node1046 := by rfl

def raw4331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw4331step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 3, 0, -1], ![3, -2, -1, 0]]

def raw4331step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -3, 0, 1], ![-3, 2, 1, 0]]

def raw4331step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

theorem canonical4331 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4331 = injectiveMoment H node1046 := by
  calc
    injectiveMoment H raw4331 = injectiveMoment H raw4331step0 := by
      have heq : raw4331step0 = raw4331.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4331).symm
    injectiveMoment H raw4331step0 = injectiveMoment H raw4331step1 := by
      have heq : raw4331step1 = -raw4331step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4331step0).symm
    injectiveMoment H raw4331step1 = injectiveMoment H raw4331step2 := by
      have heq : raw4331step2 = (fun i j => raw4331step1 (permutation9 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4331step1 permutation9 permutation26
    _ = injectiveMoment H node1046 := by rfl

def raw4332 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4332step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical4332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4332 = injectiveMoment H node2163 := by
  calc
    injectiveMoment H raw4332 = injectiveMoment H raw4332step0 := by
      have heq : raw4332step0 = (fun i j => raw4332 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4332 permutation39 permutation9
    _ = injectiveMoment H node2163 := by rfl

def raw4333 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4333step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical4333 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4333 = injectiveMoment H node2164 := by
  calc
    injectiveMoment H raw4333 = injectiveMoment H raw4333step0 := by
      have heq : raw4333step0 = (fun i j => raw4333 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4333 permutation39 permutation9
    _ = injectiveMoment H node2164 := by rfl

def raw4334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical4334 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4334 = injectiveMoment H node2174 := by
  calc
    injectiveMoment H raw4334 = injectiveMoment H raw4334step0 := by
      have heq : raw4334step0 = (fun i j => raw4334 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4334 permutation39 permutation9
    _ = injectiveMoment H node2174 := by rfl

def raw4335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical4335 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4335 = injectiveMoment H node2178 := by
  rfl

def raw4336 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

theorem canonical4336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4336 = injectiveMoment H node2179 := by
  rfl

def raw4337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

theorem canonical4337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4337 = injectiveMoment H node2180 := by
  rfl

def raw4338 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4338step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

theorem canonical4338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4338 = injectiveMoment H node2854 := by
  calc
    injectiveMoment H raw4338 = injectiveMoment H raw4338step0 := by
      have heq : raw4338step0 = (fun i j => raw4338 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4338 permutation113 permutation15
    _ = injectiveMoment H node2854 := by rfl

def raw4339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw4339step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

theorem canonical4339 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4339 = injectiveMoment H node2859 := by
  calc
    injectiveMoment H raw4339 = injectiveMoment H raw4339step0 := by
      have heq : raw4339step0 = (fun i j => raw4339 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4339 permutation113 permutation15
    _ = injectiveMoment H node2859 := by rfl

def raw4340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

theorem canonical4340 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4340 = injectiveMoment H node2181 := by
  rfl

def raw4341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

theorem canonical4341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4341 = injectiveMoment H node2855 := by
  calc
    injectiveMoment H raw4341 = injectiveMoment H raw4341step0 := by
      have heq : raw4341step0 = (fun i j => raw4341 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4341 permutation113 permutation15
    _ = injectiveMoment H node2855 := by rfl

def raw4342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical4342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4342 = injectiveMoment H node2182 := by
  rfl

def raw4343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4343step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, -1, 3, 0], ![3, 1, -4, 0]]

def raw4343step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![2, 1, -3, 0], ![-3, -1, 4, 0]]

def raw4343step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical4343 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4343 = injectiveMoment H node1163 := by
  calc
    injectiveMoment H raw4343 = injectiveMoment H raw4343step0 := by
      have heq : raw4343step0 = raw4343.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4343).symm
    injectiveMoment H raw4343step0 = injectiveMoment H raw4343step1 := by
      have heq : raw4343step1 = -raw4343step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4343step0).symm
    injectiveMoment H raw4343step1 = injectiveMoment H raw4343step2 := by
      have heq : raw4343step2 = (fun i j => raw4343step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4343step1 permutation27 permutation19
    _ = injectiveMoment H node1163 := by rfl

def raw4344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, -1, 1, 2], ![3, 1, 0, -4]]

def raw4344step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![2, 1, -1, -2], ![-3, -1, 0, 4]]

def raw4344step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical4344 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4344 = injectiveMoment H node1172 := by
  calc
    injectiveMoment H raw4344 = injectiveMoment H raw4344step0 := by
      have heq : raw4344step0 = raw4344.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4344).symm
    injectiveMoment H raw4344step0 = injectiveMoment H raw4344step1 := by
      have heq : raw4344step1 = -raw4344step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4344step0).symm
    injectiveMoment H raw4344step1 = injectiveMoment H raw4344step2 := by
      have heq : raw4344step2 = (fun i j => raw4344step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4344step1 permutation27 permutation17
    _ = injectiveMoment H node1172 := by rfl

def raw4345 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, -1, 2, 1], ![3, 1, -1, -3]]

def raw4345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -3, -1, 3]]

theorem canonical4345 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4345 = injectiveMoment H node1372 := by
  calc
    injectiveMoment H raw4345 = injectiveMoment H raw4345step0 := by
      have heq : raw4345step0 = raw4345.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4345).symm
    injectiveMoment H raw4345step0 = injectiveMoment H raw4345step1 := by
      have heq : raw4345step1 = (fun i j => raw4345step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4345step0 permutation23 permutation20
    _ = injectiveMoment H node1372 := by rfl

def raw4346 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4346step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-2, 0, 0, 2, 0], ![3, 0, -1, -1, -1]]

def raw4346step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 0, 2, 0], ![3, -1, -1, -1]]

def raw4346step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical4346 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4346 = injectiveMoment H node973 := by
  calc
    injectiveMoment H raw4346 = injectiveMoment H raw4346step0 := by
      have heq : raw4346step0 = raw4346.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4346).symm
    injectiveMoment H raw4346step0 = injectiveMoment H raw4346step1 := by
      have hz : ∀ i, raw4346step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw4346step1 = (fun i j => raw4346step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4346step0 permutation57 hz
    injectiveMoment H raw4346step1 = injectiveMoment H raw4346step2 := by
      have heq : raw4346step2 = (fun i j => raw4346step1 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4346step1 permutation32 permutation30
    _ = injectiveMoment H node973 := by rfl

def raw4347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4347step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 0, 0, 2], ![3, 0, -1, -2]]

def raw4347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![-2, 0, 2], ![3, -1, -2]]

def raw4347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

theorem canonical4347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4347 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw4347 = injectiveMoment H raw4347step0 := by
      have heq : raw4347step0 = raw4347.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4347).symm
    injectiveMoment H raw4347step0 = injectiveMoment H raw4347step1 := by
      have hz : ∀ i, raw4347step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw4347step1 = (fun i j => raw4347step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4347step0 permutation15 hz
    injectiveMoment H raw4347step1 = injectiveMoment H raw4347step2 := by
      have heq : raw4347step2 = (fun i j => raw4347step1 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4347step1 permutation28 permutation6
    _ = injectiveMoment H node274 := by rfl

def raw4348 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4348step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -1, -1], ![-2, 0, 1, 0, 1], ![3, 0, -2, 0, -1]]

def raw4348step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 0, -1, 1, 1], ![2, 0, -1, 0, -1], ![-3, 0, 2, 0, 1]]

def raw4348step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -1, 0, -1], ![-3, 2, 0, 1]]

def raw4348step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical4348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4348 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw4348 = injectiveMoment H raw4348step0 := by
      have heq : raw4348step0 = raw4348.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4348).symm
    injectiveMoment H raw4348step0 = injectiveMoment H raw4348step1 := by
      have heq : raw4348step1 = -raw4348step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4348step0).symm
    injectiveMoment H raw4348step1 = injectiveMoment H raw4348step2 := by
      have hz : ∀ i, raw4348step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw4348step2 = (fun i j => raw4348step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4348step1 permutation57 hz
    injectiveMoment H raw4348step2 = injectiveMoment H raw4348step3 := by
      have heq : raw4348step3 = (fun i j => raw4348step2 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4348step2 permutation12 permutation26
    _ = injectiveMoment H node995 := by rfl

def raw4349 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4349step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -1, -1], ![-2, 0, 2, 0, 0], ![3, 0, -3, 0, 0]]

def raw4349step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 0, -1, 1, 1], ![2, 0, -2, 0, 0], ![-3, 0, 3, 0, 0]]

def raw4349step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -2, 0, 0], ![-3, 3, 0, 0]]

def raw4349step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical4349 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4349 = injectiveMoment H node1028 := by
  calc
    injectiveMoment H raw4349 = injectiveMoment H raw4349step0 := by
      have heq : raw4349step0 = raw4349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4349).symm
    injectiveMoment H raw4349step0 = injectiveMoment H raw4349step1 := by
      have heq : raw4349step1 = -raw4349step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4349step0).symm
    injectiveMoment H raw4349step1 = injectiveMoment H raw4349step2 := by
      have hz : ∀ i, raw4349step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw4349step2 = (fun i j => raw4349step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4349step1 permutation57 hz
    injectiveMoment H raw4349step2 = injectiveMoment H raw4349step3 := by
      have heq : raw4349step3 = (fun i j => raw4349step2 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4349step2 permutation12 permutation26
    _ = injectiveMoment H node1028 := by rfl

def raw4350 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 0, 1, 1], ![3, 0, 0, -3]]

def raw4350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-2, 1, 1], ![3, 0, -3]]

def raw4350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical4350 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4350 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw4350 = injectiveMoment H raw4350step0 := by
      have heq : raw4350step0 = raw4350.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4350).symm
    injectiveMoment H raw4350step0 = injectiveMoment H raw4350step1 := by
      have hz : ∀ i, raw4350step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw4350step1 = (fun i j => raw4350step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4350step0 permutation15 hz
    injectiveMoment H raw4350step1 = injectiveMoment H raw4350step2 := by
      have heq : raw4350step2 = (fun i j => raw4350step1 (permutation19 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4350step1 permutation19 permutation6
    _ = injectiveMoment H node223 := by rfl

def raw4351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 0, 2, 0], ![3, 0, -1, -2]]

def raw4351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-2, 2, 0], ![3, -1, -2]]

def raw4351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4351 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4351 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw4351 = injectiveMoment H raw4351step0 := by
      have heq : raw4351step0 = raw4351.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4351).symm
    injectiveMoment H raw4351step0 = injectiveMoment H raw4351step1 := by
      have hz : ∀ i, raw4351step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw4351step1 = (fun i j => raw4351step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4351step0 permutation15 hz
    injectiveMoment H raw4351step1 = injectiveMoment H raw4351step2 := by
      have heq : raw4351step2 = (fun i j => raw4351step1 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4351step1 permutation32 permutation8
    _ = injectiveMoment H node184 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
