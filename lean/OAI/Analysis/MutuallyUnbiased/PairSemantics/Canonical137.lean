import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4384 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4384step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![3, -1, 0, -2]]

def raw4384step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical4384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4384 = injectiveMoment H node1198 := by
  calc
    injectiveMoment H raw4384 = injectiveMoment H raw4384step0 := by
      have heq : raw4384step0 = raw4384.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4384).symm
    injectiveMoment H raw4384step0 = injectiveMoment H raw4384step1 := by
      have heq : raw4384step1 = (fun i j => raw4384step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4384step0 permutation29 permutation18
    _ = injectiveMoment H node1198 := by rfl

def raw4385 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4385step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![3, -1, -1, -1]]

def raw4385step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical4385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4385 = injectiveMoment H node964 := by
  calc
    injectiveMoment H raw4385 = injectiveMoment H raw4385step0 := by
      have heq : raw4385step0 = raw4385.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4385).symm
    injectiveMoment H raw4385step0 = injectiveMoment H raw4385step1 := by
      have heq : raw4385step1 = (fun i j => raw4385step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4385step0 permutation29 permutation20
    _ = injectiveMoment H node964 := by rfl

def raw4386 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4386step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem canonical4386 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4386 = injectiveMoment H node2186 := by
  calc
    injectiveMoment H raw4386 = injectiveMoment H raw4386step0 := by
      have heq : raw4386step0 = (fun i j => raw4386 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4386 permutation39 permutation9
    _ = injectiveMoment H node2186 := by rfl

def raw4387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4387step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

theorem canonical4387 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4387 = injectiveMoment H node2187 := by
  calc
    injectiveMoment H raw4387 = injectiveMoment H raw4387step0 := by
      have heq : raw4387step0 = (fun i j => raw4387 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4387 permutation39 permutation9
    _ = injectiveMoment H node2187 := by rfl

def raw4388 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

theorem canonical4388 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4388 = injectiveMoment H node2196 := by
  rfl

def raw4389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical4389 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4389 = injectiveMoment H node2197 := by
  rfl

def raw4390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw4390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical4390 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4390 = injectiveMoment H node2197 := by
  calc
    injectiveMoment H raw4390 = injectiveMoment H raw4390step0 := by
      have heq : raw4390step0 = (fun i j => raw4390 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4390 permutation34 permutation9
    _ = injectiveMoment H node2197 := by rfl

def raw4391 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4391step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 2, -1, 1], ![3, -2, 0, -1]]

def raw4391step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![2, -2, 1, -1], ![-3, 2, 0, 1]]

def raw4391step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

theorem canonical4391 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4391 = injectiveMoment H node1315 := by
  calc
    injectiveMoment H raw4391 = injectiveMoment H raw4391step0 := by
      have heq : raw4391step0 = raw4391.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4391).symm
    injectiveMoment H raw4391step0 = injectiveMoment H raw4391step1 := by
      have heq : raw4391step1 = -raw4391step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4391step0).symm
    injectiveMoment H raw4391step1 = injectiveMoment H raw4391step2 := by
      have heq : raw4391step2 = (fun i j => raw4391step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4391step1 permutation16 permutation24
    _ = injectiveMoment H node1315 := by rfl

def raw4392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem canonical4392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4392 = injectiveMoment H node2198 := by
  rfl

def raw4393 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4393step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical4393 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4393 = injectiveMoment H node1503 := by
  calc
    injectiveMoment H raw4393 = injectiveMoment H raw4393step0 := by
      have heq : raw4393step0 = (fun i j => raw4393 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4393 permutation42 permutation21
    _ = injectiveMoment H node1503 := by rfl

def raw4394 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4394step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 2, 0, 0], ![3, -2, -1, 0]]

def raw4394step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical4394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4394 = injectiveMoment H node808 := by
  calc
    injectiveMoment H raw4394 = injectiveMoment H raw4394step0 := by
      have heq : raw4394step0 = raw4394.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4394).symm
    injectiveMoment H raw4394step0 = injectiveMoment H raw4394step1 := by
      have heq : raw4394step1 = (fun i j => raw4394step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4394step0 permutation28 permutation24
    _ = injectiveMoment H node808 := by rfl

def raw4395 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4395 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4395 = injectiveMoment H node2199 := by
  rfl

def raw4396 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4396step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4396 = injectiveMoment H node2199 := by
  calc
    injectiveMoment H raw4396 = injectiveMoment H raw4396step0 := by
      have heq : raw4396step0 = (fun i j => raw4396 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4396 permutation34 permutation9
    _ = injectiveMoment H node2199 := by rfl

def raw4397 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw4397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 2, 1, -1], ![3, -2, -2, 1]]

def raw4397step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, -1, -2]]

theorem canonical4397 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4397 = injectiveMoment H node407 := by
  calc
    injectiveMoment H raw4397 = injectiveMoment H raw4397step0 := by
      have heq : raw4397step0 = raw4397.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4397).symm
    injectiveMoment H raw4397step0 = injectiveMoment H raw4397step1 := by
      have heq : raw4397step1 = (fun i j => raw4397step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4397step0 permutation27 permutation18
    _ = injectiveMoment H node407 := by rfl

def raw4398 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, 0, -2]]

def raw4398step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical4398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4398 = injectiveMoment H node408 := by
  calc
    injectiveMoment H raw4398 = injectiveMoment H raw4398step0 := by
      have heq : raw4398step0 = (fun i j => raw4398 (permutation12 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4398 permutation12 permutation21
    _ = injectiveMoment H node408 := by rfl

def raw4399 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4399step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 2, 1, -1], ![3, -2, 0, -1]]

def raw4399step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem canonical4399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4399 = injectiveMoment H node484 := by
  calc
    injectiveMoment H raw4399 = injectiveMoment H raw4399step0 := by
      have heq : raw4399step0 = raw4399.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4399).symm
    injectiveMoment H raw4399step0 = injectiveMoment H raw4399step1 := by
      have heq : raw4399step1 = (fun i j => raw4399step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4399step0 permutation29 permutation20
    _ = injectiveMoment H node484 := by rfl

def raw4400 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw4400step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

theorem canonical4400 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4400 = injectiveMoment H node1351 := by
  calc
    injectiveMoment H raw4400 = injectiveMoment H raw4400step0 := by
      have heq : raw4400step0 = (fun i j => raw4400 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4400 permutation24 permutation15
    _ = injectiveMoment H node1351 := by rfl

def raw4401 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4401step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![3, -2, 0, -1]]

def raw4401step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -2, 0, 0], ![-3, 2, 0, 1]]

def raw4401step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical4401 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4401 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw4401 = injectiveMoment H raw4401step0 := by
      have heq : raw4401step0 = raw4401.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4401).symm
    injectiveMoment H raw4401step0 = injectiveMoment H raw4401step1 := by
      have heq : raw4401step1 = -raw4401step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4401step0).symm
    injectiveMoment H raw4401step1 = injectiveMoment H raw4401step2 := by
      have heq : raw4401step2 = (fun i j => raw4401step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4401step1 permutation11 permutation32
    _ = injectiveMoment H node1032 := by rfl

def raw4402 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4402step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 2, 1, -1], ![3, -2, -1, 0]]

def raw4402step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -2, -1, 1], ![-3, 2, 1, 0]]

def raw4402step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical4402 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4402 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw4402 = injectiveMoment H raw4402step0 := by
      have heq : raw4402step0 = raw4402.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4402).symm
    injectiveMoment H raw4402step0 = injectiveMoment H raw4402step1 := by
      have heq : raw4402step1 = -raw4402step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4402step0).symm
    injectiveMoment H raw4402step1 = injectiveMoment H raw4402step2 := by
      have heq : raw4402step2 = (fun i j => raw4402step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4402step1 permutation10 permutation32
    _ = injectiveMoment H node1083 := by rfl

def raw4403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw4403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-2, 2, -1, 1], ![3, -2, 0, -1]]

def raw4403step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![2, -2, 1, -1], ![-3, 2, 0, 1]]

def raw4403step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical4403 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4403 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw4403 = injectiveMoment H raw4403step0 := by
      have heq : raw4403step0 = raw4403.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4403).symm
    injectiveMoment H raw4403step0 = injectiveMoment H raw4403step1 := by
      have heq : raw4403step1 = -raw4403step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4403step0).symm
    injectiveMoment H raw4403step1 = injectiveMoment H raw4403step2 := by
      have heq : raw4403step2 = (fun i j => raw4403step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4403step1 permutation10 permutation26
    _ = injectiveMoment H node1083 := by rfl

def raw4404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, 0, 1, -2], ![1, -1, -1, 1]]

def raw4404step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

theorem canonical4404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4404 = injectiveMoment H node1351 := by
  calc
    injectiveMoment H raw4404 = injectiveMoment H raw4404step0 := by
      have heq : raw4404step0 = (fun i j => raw4404 (permutation30 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4404 permutation30 permutation15
    _ = injectiveMoment H node1351 := by rfl

def raw4405 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical4405 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4405 = injectiveMoment H node2200 := by
  rfl

def raw4406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 3, -1, 0], ![3, -3, 0, 0]]

def raw4406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 0, -3, 3], ![0, 2, 0, -2], ![1, -2, 0, 1]]

theorem canonical4406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4406 = injectiveMoment H node1321 := by
  calc
    injectiveMoment H raw4406 = injectiveMoment H raw4406step0 := by
      have heq : raw4406step0 = raw4406.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4406).symm
    injectiveMoment H raw4406step0 = injectiveMoment H raw4406step1 := by
      have heq : raw4406step1 = (fun i j => raw4406step0 (permutation25 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4406step0 permutation25 permutation26
    _ = injectiveMoment H node1321 := by rfl

def raw4407 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4407 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4407 = injectiveMoment H node2201 := by
  rfl

def raw4408 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4408step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4408 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4408 = injectiveMoment H node2201 := by
  calc
    injectiveMoment H raw4408 = injectiveMoment H raw4408step0 := by
      have heq : raw4408step0 = (fun i j => raw4408 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4408 permutation34 permutation9
    _ = injectiveMoment H node2201 := by rfl

def raw4409 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4409step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 3, 0, -1], ![3, -3, -1, 1]]

def raw4409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 3, -1, -2], ![1, 0, -2, 1]]

theorem canonical4409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4409 = injectiveMoment H node727 := by
  calc
    injectiveMoment H raw4409 = injectiveMoment H raw4409step0 := by
      have heq : raw4409step0 = raw4409.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4409).symm
    injectiveMoment H raw4409step0 = injectiveMoment H raw4409step1 := by
      have heq : raw4409step1 = (fun i j => raw4409step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4409step0 permutation28 permutation24
    _ = injectiveMoment H node727 := by rfl

def raw4410 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]

theorem canonical4410 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4410 = injectiveMoment H node675 := by
  rfl

def raw4411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 3, -1, 0], ![3, -3, 1, -1]]

def raw4411step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -3, 1, 0], ![-3, 3, -1, 1]]

def raw4411step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical4411 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4411 = injectiveMoment H node1072 := by
  calc
    injectiveMoment H raw4411 = injectiveMoment H raw4411step0 := by
      have heq : raw4411step0 = raw4411.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4411).symm
    injectiveMoment H raw4411step0 = injectiveMoment H raw4411step1 := by
      have heq : raw4411step1 = -raw4411step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4411step0).symm
    injectiveMoment H raw4411step1 = injectiveMoment H raw4411step2 := by
      have heq : raw4411step2 = (fun i j => raw4411step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4411step1 permutation11 permutation32
    _ = injectiveMoment H node1072 := by rfl

def raw4412 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 3, 0, -1], ![3, -3, 0, 0]]

def raw4412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -3, 0, 1], ![-3, 3, 0, 0]]

def raw4412step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

theorem canonical4412 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4412 = injectiveMoment H node1062 := by
  calc
    injectiveMoment H raw4412 = injectiveMoment H raw4412step0 := by
      have heq : raw4412step0 = raw4412.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4412).symm
    injectiveMoment H raw4412step0 = injectiveMoment H raw4412step1 := by
      have heq : raw4412step1 = -raw4412step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4412step0).symm
    injectiveMoment H raw4412step1 = injectiveMoment H raw4412step2 := by
      have heq : raw4412step2 = (fun i j => raw4412step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4412step1 permutation14 permutation26
    _ = injectiveMoment H node1062 := by rfl

def raw4413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw4413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-2, 3, -1, 0], ![3, -3, 0, 0]]

def raw4413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![2, -3, 1, 0], ![-3, 3, 0, 0]]

def raw4413step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

theorem canonical4413 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4413 = injectiveMoment H node1062 := by
  calc
    injectiveMoment H raw4413 = injectiveMoment H raw4413step0 := by
      have heq : raw4413step0 = raw4413.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4413).symm
    injectiveMoment H raw4413step0 = injectiveMoment H raw4413step1 := by
      have heq : raw4413step1 = -raw4413step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4413step0).symm
    injectiveMoment H raw4413step1 = injectiveMoment H raw4413step2 := by
      have heq : raw4413step2 = (fun i j => raw4413step1 (permutation14 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4413step1 permutation14 permutation32
    _ = injectiveMoment H node1062 := by rfl

def raw4414 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4414step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 0, 3], ![3, 0, 1, -4]]

def raw4414step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 1, 0]]

theorem canonical4414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4414 = injectiveMoment H node1230 := by
  calc
    injectiveMoment H raw4414 = injectiveMoment H raw4414step0 := by
      have heq : raw4414step0 = raw4414.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4414).symm
    injectiveMoment H raw4414step0 = injectiveMoment H raw4414step1 := by
      have heq : raw4414step1 = (fun i j => raw4414step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4414step0 permutation22 permutation17
    _ = injectiveMoment H node1230 := by rfl

def raw4415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw4415step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 1, 2], ![3, 0, 0, -3]]

def raw4415step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

theorem canonical4415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4415 = injectiveMoment H node1369 := by
  calc
    injectiveMoment H raw4415 = injectiveMoment H raw4415step0 := by
      have heq : raw4415step0 = raw4415.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4415).symm
    injectiveMoment H raw4415step0 = injectiveMoment H raw4415step1 := by
      have heq : raw4415step1 = (fun i j => raw4415step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4415step0 permutation25 permutation18
    _ = injectiveMoment H node1369 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
