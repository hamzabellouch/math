import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 2, 1], ![3, 0, -1, -2]]

def raw4416step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, 1, -2, -1], ![-3, 0, 1, 2]]

def raw4416step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical4416 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4416 = injectiveMoment H node1310 := by
  calc
    injectiveMoment H raw4416 = injectiveMoment H raw4416step0 := by
      have heq : raw4416step0 = raw4416.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4416).symm
    injectiveMoment H raw4416step0 = injectiveMoment H raw4416step1 := by
      have heq : raw4416step1 = -raw4416step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4416step0).symm
    injectiveMoment H raw4416step1 = injectiveMoment H raw4416step2 := by
      have heq : raw4416step2 = (fun i j => raw4416step1 (permutation16 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4416step1 permutation16 permutation20
    _ = injectiveMoment H node1310 := by rfl

def raw4417 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4417step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 3, 0], ![3, 0, -2, -1]]

def raw4417step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical4417 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4417 = injectiveMoment H node1210 := by
  calc
    injectiveMoment H raw4417 = injectiveMoment H raw4417step0 := by
      have heq : raw4417step0 = raw4417.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4417).symm
    injectiveMoment H raw4417step0 = injectiveMoment H raw4417step1 := by
      have heq : raw4417step1 = (fun i j => raw4417step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4417step0 permutation25 permutation19
    _ = injectiveMoment H node1210 := by rfl

def raw4418 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4418step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, -1, 0, 3], ![3, 0, 0, -3]]

def raw4418step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 1, -1]]

theorem canonical4418 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4418 = injectiveMoment H node1224 := by
  calc
    injectiveMoment H raw4418 = injectiveMoment H raw4418step0 := by
      have heq : raw4418step0 = raw4418.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4418).symm
    injectiveMoment H raw4418step0 = injectiveMoment H raw4418step1 := by
      have heq : raw4418step1 = (fun i j => raw4418step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4418step0 permutation25 permutation17
    _ = injectiveMoment H node1224 := by rfl

def raw4419 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, -1, 1, 2], ![3, 0, -1, -2]]

def raw4419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, 1, -1, -2], ![-3, 0, 1, 2]]

def raw4419step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical4419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4419 = injectiveMoment H node1361 := by
  calc
    injectiveMoment H raw4419 = injectiveMoment H raw4419step0 := by
      have heq : raw4419step0 = raw4419.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4419).symm
    injectiveMoment H raw4419step0 = injectiveMoment H raw4419step1 := by
      have heq : raw4419step1 = -raw4419step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4419step0).symm
    injectiveMoment H raw4419step1 = injectiveMoment H raw4419step2 := by
      have heq : raw4419step2 = (fun i j => raw4419step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4419step1 permutation16 permutation18
    _ = injectiveMoment H node1361 := by rfl

def raw4420 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw4420step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, -1, 2, 1], ![3, 0, -2, -1]]

def raw4420step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, 1, -2, -1], ![-3, 0, 2, 1]]

def raw4420step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical4420 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4420 = injectiveMoment H node1361 := by
  calc
    injectiveMoment H raw4420 = injectiveMoment H raw4420step0 := by
      have heq : raw4420step0 = raw4420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4420).symm
    injectiveMoment H raw4420step0 = injectiveMoment H raw4420step1 := by
      have heq : raw4420step1 = -raw4420step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4420step0).symm
    injectiveMoment H raw4420step1 = injectiveMoment H raw4420step2 := by
      have heq : raw4420step2 = (fun i j => raw4420step1 (permutation16 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4420step1 permutation16 permutation20
    _ = injectiveMoment H node1361 := by rfl

def raw4421 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4421step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 0, 2, 0], ![3, -1, -1, -1]]

def raw4421step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical4421 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4421 = injectiveMoment H node973 := by
  calc
    injectiveMoment H raw4421 = injectiveMoment H raw4421step0 := by
      have heq : raw4421step0 = raw4421.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4421).symm
    injectiveMoment H raw4421step0 = injectiveMoment H raw4421step1 := by
      have heq : raw4421step1 = (fun i j => raw4421step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4421step0 permutation32 permutation30
    _ = injectiveMoment H node973 := by rfl

def raw4422 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4422step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 0, 3, -1], ![3, -1, -2, 0]]

def raw4422step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

theorem canonical4422 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4422 = injectiveMoment H node1213 := by
  calc
    injectiveMoment H raw4422 = injectiveMoment H raw4422step0 := by
      have heq : raw4422step0 = raw4422.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4422).symm
    injectiveMoment H raw4422step0 = injectiveMoment H raw4422step1 := by
      have heq : raw4422step1 = (fun i j => raw4422step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4422step0 permutation31 permutation20
    _ = injectiveMoment H node1213 := by rfl

def raw4423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 0, -1, 3], ![3, -1, 1, -3]]

def raw4423step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical4423 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4423 = injectiveMoment H node1327 := by
  calc
    injectiveMoment H raw4423 = injectiveMoment H raw4423step0 := by
      have heq : raw4423step0 = raw4423.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4423).symm
    injectiveMoment H raw4423step0 = injectiveMoment H raw4423step1 := by
      have heq : raw4423step1 = (fun i j => raw4423step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4423step0 permutation31 permutation18
    _ = injectiveMoment H node1327 := by rfl

def raw4424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 0, 0, 2], ![3, -1, 0, -2]]

def raw4424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical4424 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4424 = injectiveMoment H node1222 := by
  calc
    injectiveMoment H raw4424 = injectiveMoment H raw4424step0 := by
      have heq : raw4424step0 = raw4424.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4424).symm
    injectiveMoment H raw4424step0 = injectiveMoment H raw4424step1 := by
      have heq : raw4424step1 = (fun i j => raw4424step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4424step0 permutation31 permutation18
    _ = injectiveMoment H node1222 := by rfl

def raw4425 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4425step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 0, 1, 1], ![3, -1, -1, -1]]

def raw4425step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical4425 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4425 = injectiveMoment H node987 := by
  calc
    injectiveMoment H raw4425 = injectiveMoment H raw4425step0 := by
      have heq : raw4425step0 = raw4425.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4425).symm
    injectiveMoment H raw4425step0 = injectiveMoment H raw4425step1 := by
      have heq : raw4425step1 = (fun i j => raw4425step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4425step0 permutation28 permutation18
    _ = injectiveMoment H node987 := by rfl

def raw4426 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4426step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 1, 1, 0], ![3, -2, 0, -1]]

def raw4426step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical4426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4426 = injectiveMoment H node815 := by
  calc
    injectiveMoment H raw4426 = injectiveMoment H raw4426step0 := by
      have heq : raw4426step0 = raw4426.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4426).symm
    injectiveMoment H raw4426step0 = injectiveMoment H raw4426step1 := by
      have heq : raw4426step1 = (fun i j => raw4426step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4426step0 permutation30 permutation30
    _ = injectiveMoment H node815 := by rfl

def raw4427 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4427step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 1, 2, -1], ![3, -2, -1, 0]]

def raw4427step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, -1, -2, 1], ![-3, 2, 1, 0]]

def raw4427step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical4427 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4427 = injectiveMoment H node1248 := by
  calc
    injectiveMoment H raw4427 = injectiveMoment H raw4427step0 := by
      have heq : raw4427step0 = raw4427.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4427).symm
    injectiveMoment H raw4427step0 = injectiveMoment H raw4427step1 := by
      have heq : raw4427step1 = -raw4427step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4427step0).symm
    injectiveMoment H raw4427step1 = injectiveMoment H raw4427step2 := by
      have heq : raw4427step2 = (fun i j => raw4427step1 (permutation10 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4427step1 permutation10 permutation30
    _ = injectiveMoment H node1248 := by rfl

def raw4428 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem canonical4428 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4428 = injectiveMoment H node676 := by
  rfl

def raw4429 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4429step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 1, 0, 1], ![3, -2, 0, -1]]

def raw4429step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -1, 0, -1], ![-3, 2, 0, 1]]

def raw4429step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical4429 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4429 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw4429 = injectiveMoment H raw4429step0 := by
      have heq : raw4429step0 = raw4429.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4429).symm
    injectiveMoment H raw4429step0 = injectiveMoment H raw4429step1 := by
      have heq : raw4429step1 = -raw4429step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4429step0).symm
    injectiveMoment H raw4429step1 = injectiveMoment H raw4429step2 := by
      have heq : raw4429step2 = (fun i j => raw4429step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4429step1 permutation12 permutation26
    _ = injectiveMoment H node995 := by rfl

def raw4430 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4430step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 2, 1, -1], ![3, -3, 0, 0]]

def raw4430step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, -2, -1, 1], ![-3, 3, 0, 0]]

def raw4430step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

theorem canonical4430 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4430 = injectiveMoment H node1067 := by
  calc
    injectiveMoment H raw4430 = injectiveMoment H raw4430step0 := by
      have heq : raw4430step0 = raw4430.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4430).symm
    injectiveMoment H raw4430step0 = injectiveMoment H raw4430step1 := by
      have heq : raw4430step1 = -raw4430step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4430step0).symm
    injectiveMoment H raw4430step1 = injectiveMoment H raw4430step2 := by
      have heq : raw4430step2 = (fun i j => raw4430step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4430step1 permutation13 permutation32
    _ = injectiveMoment H node1067 := by rfl

def raw4431 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical4431 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4431 = injectiveMoment H node677 := by
  rfl

def raw4432 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4432step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 2, 0, 0], ![3, -3, 0, 0]]

def raw4432step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -2, 0, 0], ![-3, 3, 0, 0]]

def raw4432step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical4432 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4432 = injectiveMoment H node1028 := by
  calc
    injectiveMoment H raw4432 = injectiveMoment H raw4432step0 := by
      have heq : raw4432step0 = raw4432.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4432).symm
    injectiveMoment H raw4432step0 = injectiveMoment H raw4432step1 := by
      have heq : raw4432step1 = -raw4432step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4432step0).symm
    injectiveMoment H raw4432step1 = injectiveMoment H raw4432step2 := by
      have heq : raw4432step2 = (fun i j => raw4432step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4432step1 permutation12 permutation26
    _ = injectiveMoment H node1028 := by rfl

def raw4433 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4433step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 3, 0, -1], ![3, -4, 1, 0]]

def raw4433step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, -3, 0, 1], ![-3, 4, -1, 0]]

def raw4433step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, 0, -3, 2]]

theorem canonical4433 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4433 = injectiveMoment H node1020 := by
  calc
    injectiveMoment H raw4433 = injectiveMoment H raw4433step0 := by
      have heq : raw4433step0 = raw4433.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4433).symm
    injectiveMoment H raw4433step0 = injectiveMoment H raw4433step1 := by
      have heq : raw4433step1 = -raw4433step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4433step0).symm
    injectiveMoment H raw4433step1 = injectiveMoment H raw4433step2 := by
      have heq : raw4433step2 = (fun i j => raw4433step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4433step1 permutation13 permutation32
    _ = injectiveMoment H node1020 := by rfl

def raw4434 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4434step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 3, -1, 0], ![3, -4, 1, 0]]

def raw4434step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -3, 1, 0], ![-3, 4, -1, 0]]

def raw4434step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 1, -3, 2], ![1, 1, -1, -1]]

theorem canonical4434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4434 = injectiveMoment H node1019 := by
  calc
    injectiveMoment H raw4434 = injectiveMoment H raw4434step0 := by
      have heq : raw4434step0 = raw4434.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4434).symm
    injectiveMoment H raw4434step0 = injectiveMoment H raw4434step1 := by
      have heq : raw4434step1 = -raw4434step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4434step0).symm
    injectiveMoment H raw4434step1 = injectiveMoment H raw4434step2 := by
      have heq : raw4434step2 = (fun i j => raw4434step1 (permutation14 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4434step1 permutation14 permutation32
    _ = injectiveMoment H node1019 := by rfl

def raw4435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4435step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 3, 0, -1], ![3, -4, 0, 1]]

def raw4435step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -3, 0, 1], ![-3, 4, 0, -1]]

def raw4435step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 1, -3, 2], ![1, 1, -1, -1]]

theorem canonical4435 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4435 = injectiveMoment H node1019 := by
  calc
    injectiveMoment H raw4435 = injectiveMoment H raw4435step0 := by
      have heq : raw4435step0 = raw4435.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4435).symm
    injectiveMoment H raw4435step0 = injectiveMoment H raw4435step1 := by
      have heq : raw4435step1 = -raw4435step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4435step0).symm
    injectiveMoment H raw4435step1 = injectiveMoment H raw4435step2 := by
      have heq : raw4435step2 = (fun i j => raw4435step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4435step1 permutation14 permutation26
    _ = injectiveMoment H node1019 := by rfl

def raw4436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw4436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw4436step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 2, -1, 0], ![2, -2, -1, 1], ![-3, 1, 2, 0]]

def raw4436step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical4436 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4436 = injectiveMoment H node1248 := by
  calc
    injectiveMoment H raw4436 = injectiveMoment H raw4436step0 := by
      have heq : raw4436step0 = raw4436.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4436).symm
    injectiveMoment H raw4436step0 = injectiveMoment H raw4436step1 := by
      have heq : raw4436step1 = -raw4436step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4436step0).symm
    injectiveMoment H raw4436step1 = injectiveMoment H raw4436step2 := by
      have heq : raw4436step2 = (fun i j => raw4436step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4436step1 permutation10 permutation32
    _ = injectiveMoment H node1248 := by rfl

def raw4437 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![1, -1, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4437step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem canonical4437 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4437 = injectiveMoment H node676 := by
  calc
    injectiveMoment H raw4437 = injectiveMoment H raw4437step0 := by
      have heq : raw4437step0 = (fun i j => raw4437 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4437 permutation12 permutation9
    _ = injectiveMoment H node676 := by rfl

def raw4438 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4438step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

theorem canonical4438 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4438 = injectiveMoment H node2051 := by
  calc
    injectiveMoment H raw4438 = injectiveMoment H raw4438step0 := by
      have heq : raw4438step0 = (fun i j => raw4438 (permutation72 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4438 permutation72 permutation15
    _ = injectiveMoment H node2051 := by rfl

def raw4439 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw4439step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-1, 0, 3, -2], ![2, 2, -4, 0]]

def raw4439step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -1, 0], ![1, 0, -3, 2], ![-2, -2, 4, 0]]

def raw4439step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

theorem canonical4439 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4439 = injectiveMoment H node577 := by
  calc
    injectiveMoment H raw4439 = injectiveMoment H raw4439step0 := by
      have heq : raw4439step0 = raw4439.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4439).symm
    injectiveMoment H raw4439step0 = injectiveMoment H raw4439step1 := by
      have heq : raw4439step1 = -raw4439step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4439step0).symm
    injectiveMoment H raw4439step1 = injectiveMoment H raw4439step2 := by
      have heq : raw4439step2 = (fun i j => raw4439step1 (permutation28 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4439step1 permutation28 permutation19
    _ = injectiveMoment H node577 := by rfl

def raw4440 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 0, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def raw4440step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-1, 0, 3, -2], ![2, 2, -4, 0]]

def raw4440step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 2, 0, -1], ![1, 0, -3, 2], ![-2, -2, 4, 0]]

def raw4440step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

theorem canonical4440 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4440 = injectiveMoment H node580 := by
  calc
    injectiveMoment H raw4440 = injectiveMoment H raw4440step0 := by
      have heq : raw4440step0 = raw4440.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4440).symm
    injectiveMoment H raw4440step0 = injectiveMoment H raw4440step1 := by
      have heq : raw4440step1 = -raw4440step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4440step0).symm
    injectiveMoment H raw4440step1 = injectiveMoment H raw4440step2 := by
      have heq : raw4440step2 = (fun i j => raw4440step1 (permutation28 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4440step1 permutation28 permutation19
    _ = injectiveMoment H node580 := by rfl

def raw4441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw4441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

theorem canonical4441 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4441 = injectiveMoment H node618 := by
  calc
    injectiveMoment H raw4441 = injectiveMoment H raw4441step0 := by
      have heq : raw4441step0 = (fun i j => raw4441 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4441 permutation17 permutation15
    _ = injectiveMoment H node618 := by rfl

def raw4442 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4442step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-1, 1, -1, 1], ![2, 1, 0, -3]]

def raw4442step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 2, 0, -1], ![1, -1, 1, -1], ![-2, -1, 0, 3]]

def raw4442step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical4442 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4442 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw4442 = injectiveMoment H raw4442step0 := by
      have heq : raw4442step0 = raw4442.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4442).symm
    injectiveMoment H raw4442step0 = injectiveMoment H raw4442step1 := by
      have heq : raw4442step1 = -raw4442step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4442step0).symm
    injectiveMoment H raw4442step1 = injectiveMoment H raw4442step2 := by
      have heq : raw4442step2 = (fun i j => raw4442step1 (permutation13 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4442step1 permutation13 permutation24
    _ = injectiveMoment H node1249 := by rfl

def raw4443 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw4443step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical4443 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4443 = injectiveMoment H node513 := by
  calc
    injectiveMoment H raw4443 = injectiveMoment H raw4443step0 := by
      have heq : raw4443step0 = (fun i j => raw4443 (permutation10 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4443 permutation10 permutation11
    _ = injectiveMoment H node513 := by rfl

def raw4444 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4444step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical4444 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4444 = injectiveMoment H node1752 := by
  calc
    injectiveMoment H raw4444 = injectiveMoment H raw4444step0 := by
      have heq : raw4444step0 = (fun i j => raw4444 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4444 permutation39 permutation11
    _ = injectiveMoment H node1752 := by rfl

def raw4445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw4445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-1, 2, -1, 0], ![2, 0, 0, -2]]

def raw4445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical4445 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4445 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw4445 = injectiveMoment H raw4445step0 := by
      have heq : raw4445step0 = raw4445.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4445).symm
    injectiveMoment H raw4445step0 = injectiveMoment H raw4445step1 := by
      have heq : raw4445step1 = (fun i j => raw4445step0 (permutation25 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4445step0 permutation25 permutation26
    _ = injectiveMoment H node1304 := by rfl

def raw4446 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4446step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-1, 2, 0, -1], ![2, 0, -1, -1]]

def raw4446step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical4446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4446 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw4446 = injectiveMoment H raw4446step0 := by
      have heq : raw4446step0 = raw4446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4446).symm
    injectiveMoment H raw4446step0 = injectiveMoment H raw4446step1 := by
      have heq : raw4446step1 = (fun i j => raw4446step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4446step0 permutation31 permutation26
    _ = injectiveMoment H node1010 := by rfl

def raw4447 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4447step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-1, 2, 0, -1], ![2, 0, -1, -1]]

def raw4447step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical4447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4447 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw4447 = injectiveMoment H raw4447step0 := by
      have heq : raw4447step0 = raw4447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4447).symm
    injectiveMoment H raw4447step0 = injectiveMoment H raw4447step1 := by
      have heq : raw4447step1 = (fun i j => raw4447step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4447step0 permutation32 permutation26
    _ = injectiveMoment H node1005 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
