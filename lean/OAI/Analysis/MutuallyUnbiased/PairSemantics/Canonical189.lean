import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6048 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6048 = injectiveMoment H node899 := by
  rfl

def raw6049 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical6049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6049 = injectiveMoment H node902 := by
  rfl

def raw6050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical6050 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6050 = injectiveMoment H node903 := by
  rfl

def raw6051 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![1, 2, -1, -2]]

def raw6051step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1], ![4, -2, -2]]

def raw6051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![2, -3, 1], ![-4, 2, 2]]

def raw6051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical6051 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6051 = injectiveMoment H node106 := by
  calc
    injectiveMoment H raw6051 = injectiveMoment H raw6051step0 := by
      have heq : raw6051step0 = raw6051.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6051).symm
    injectiveMoment H raw6051step0 = injectiveMoment H raw6051step1 := by
      have heq : raw6051step1 = -raw6051step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6051step0).symm
    injectiveMoment H raw6051step1 = injectiveMoment H raw6051step2 := by
      have heq : raw6051step2 = (fun i j => raw6051step1 (permutation21 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6051step1 permutation21 permutation6
    _ = injectiveMoment H node106 := by rfl

def raw6052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6052step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-2, 0, 1, 1], ![4, 0, -2, -2]]

def raw6052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, 1, 1], ![4, -2, -2]]

def raw6052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6052 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw6052 = injectiveMoment H raw6052step0 := by
      have heq : raw6052step0 = raw6052.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6052).symm
    injectiveMoment H raw6052step0 = injectiveMoment H raw6052step1 := by
      have hz : ∀ i, raw6052step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw6052step1 = (fun i j => raw6052step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6052step0 permutation15 hz
    injectiveMoment H raw6052step1 = injectiveMoment H raw6052step2 := by
      have heq : raw6052step2 = (fun i j => raw6052step1 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6052step1 permutation27 permutation6
    _ = injectiveMoment H node150 := by rfl

def raw6053 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6053step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6053 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6053 = injectiveMoment H node2487 := by
  calc
    injectiveMoment H raw6053 = injectiveMoment H raw6053step0 := by
      have heq : raw6053step0 = (fun i j => raw6053 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6053 permutation39 permutation9
    _ = injectiveMoment H node2487 := by rfl

def raw6054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

theorem canonical6054 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6054 = injectiveMoment H node2486 := by
  calc
    injectiveMoment H raw6054 = injectiveMoment H raw6054step0 := by
      have heq : raw6054step0 = (fun i j => raw6054 (permutation45 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6054 permutation45 permutation15
    _ = injectiveMoment H node2486 := by rfl

def raw6055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6055step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 2, -4], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw6055step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

theorem canonical6055 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6055 = injectiveMoment H node2256 := by
  calc
    injectiveMoment H raw6055 = injectiveMoment H raw6055step0 := by
      have heq : raw6055step0 = -raw6055 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6055).symm
    injectiveMoment H raw6055step0 = injectiveMoment H raw6055step1 := by
      have heq : raw6055step1 = (fun i j => raw6055step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6055step0 permutation101 permutation15
    _ = injectiveMoment H node2256 := by rfl

def raw6056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6056step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6056 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6056 = injectiveMoment H node2496 := by
  calc
    injectiveMoment H raw6056 = injectiveMoment H raw6056step0 := by
      have heq : raw6056step0 = (fun i j => raw6056 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6056 permutation39 permutation9
    _ = injectiveMoment H node2496 := by rfl

def raw6057 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6057step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical6057 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6057 = injectiveMoment H node2497 := by
  calc
    injectiveMoment H raw6057 = injectiveMoment H raw6057step0 := by
      have heq : raw6057step0 = (fun i j => raw6057 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6057 permutation39 permutation9
    _ = injectiveMoment H node2497 := by rfl

def raw6058 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw6058step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical6058 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6058 = injectiveMoment H node2498 := by
  calc
    injectiveMoment H raw6058 = injectiveMoment H raw6058step0 := by
      have heq : raw6058step0 = (fun i j => raw6058 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6058 permutation39 permutation9
    _ = injectiveMoment H node2498 := by rfl

def raw6059 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6059 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6059 = injectiveMoment H node910 := by
  calc
    injectiveMoment H raw6059 = injectiveMoment H raw6059step0 := by
      have hz : ∀ j, raw6059 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw6059step0 = (fun i j => raw6059 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6059 permutation80 hz
    _ = injectiveMoment H node910 := by rfl

def raw6060 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem canonical6060 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6060 = injectiveMoment H node2501 := by
  rfl

def raw6061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6061 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6061 = injectiveMoment H node2503 := by
  rfl

def raw6062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6062step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6062 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6062 = injectiveMoment H node2502 := by
  calc
    injectiveMoment H raw6062 = injectiveMoment H raw6062step0 := by
      have heq : raw6062step0 = (fun i j => raw6062 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6062 permutation34 permutation15
    _ = injectiveMoment H node2502 := by rfl

def raw6063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical6063 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6063 = injectiveMoment H node2504 := by
  rfl

def raw6064 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6064step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6064 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6064 = injectiveMoment H node2403 := by
  calc
    injectiveMoment H raw6064 = injectiveMoment H raw6064step0 := by
      have heq : raw6064step0 = (fun i j => raw6064 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6064 permutation45 permutation11
    _ = injectiveMoment H node2403 := by rfl

def raw6065 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, 2, -1, -1]]

def raw6065step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical6065 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6065 = injectiveMoment H node2504 := by
  calc
    injectiveMoment H raw6065 = injectiveMoment H raw6065step0 := by
      have heq : raw6065step0 = (fun i j => raw6065 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6065 permutation34 permutation9
    _ = injectiveMoment H node2504 := by rfl

def raw6066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical6066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6066 = injectiveMoment H node906 := by
  rfl

def raw6067 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical6067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6067 = injectiveMoment H node2506 := by
  rfl

def raw6068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical6068 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6068 = injectiveMoment H node907 := by
  rfl

def raw6069 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, 1, -2]]

def raw6069step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6069 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6069 = injectiveMoment H node2502 := by
  calc
    injectiveMoment H raw6069 = injectiveMoment H raw6069step0 := by
      have heq : raw6069step0 = (fun i j => raw6069 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6069 permutation35 permutation9
    _ = injectiveMoment H node2502 := by rfl

def raw6070 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical6070 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6070 = injectiveMoment H node2507 := by
  rfl

def raw6071 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6071 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6071 = injectiveMoment H node909 := by
  rfl

def raw6072 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw6072step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6072 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6072 = injectiveMoment H node2505 := by
  calc
    injectiveMoment H raw6072 = injectiveMoment H raw6072step0 := by
      have heq : raw6072step0 = (fun i j => raw6072 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6072 permutation36 permutation15
    _ = injectiveMoment H node2505 := by rfl

def raw6073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![0, 1, -1, 0]]

def raw6073step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical6073 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6073 = injectiveMoment H node2507 := by
  calc
    injectiveMoment H raw6073 = injectiveMoment H raw6073step0 := by
      have heq : raw6073step0 = (fun i j => raw6073 (permutation37 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6073 permutation37 permutation9
    _ = injectiveMoment H node2507 := by rfl

def raw6074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6074 = injectiveMoment H node910 := by
  rfl

def raw6075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![1, 1, -1, -1]]

def raw6075step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6075 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6075 = injectiveMoment H node2490 := by
  calc
    injectiveMoment H raw6075 = injectiveMoment H raw6075step0 := by
      have heq : raw6075step0 = (fun i j => raw6075 (permutation45 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6075 permutation45 permutation9
    _ = injectiveMoment H node2490 := by rfl

def raw6076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![0, 1, 0, -1]]

def raw6076step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6076 = injectiveMoment H node2401 := by
  calc
    injectiveMoment H raw6076 = injectiveMoment H raw6076step0 := by
      have heq : raw6076step0 = (fun i j => raw6076 (permutation51 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6076 permutation51 permutation11
    _ = injectiveMoment H node2401 := by rfl

def raw6077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6077step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6077 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6077 = injectiveMoment H node910 := by
  calc
    injectiveMoment H raw6077 = injectiveMoment H raw6077step0 := by
      have heq : raw6077step0 = (fun i j => raw6077 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6077 permutation10 permutation15
    _ = injectiveMoment H node910 := by rfl

def raw6078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6078step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6078 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6078 = injectiveMoment H node909 := by
  calc
    injectiveMoment H raw6078 = injectiveMoment H raw6078step0 := by
      have heq : raw6078step0 = (fun i j => raw6078 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6078 permutation10 permutation15
    _ = injectiveMoment H node909 := by rfl

def raw6079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical6079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6079 = injectiveMoment H node911 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
