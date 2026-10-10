import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4064 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw4064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw4064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]

def raw4064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical4064 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4064 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw4064 = injectiveMoment H raw4064step0 := by
      have heq : raw4064step0 = -raw4064 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4064).symm
    injectiveMoment H raw4064step0 = injectiveMoment H raw4064step1 := by
      have hz : ∀ j, raw4064step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4064step1 = (fun i j => raw4064step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4064step0 permutation80 hz
    injectiveMoment H raw4064step1 = injectiveMoment H raw4064step2 := by
      have heq : raw4064step2 = (fun i j => raw4064step1 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4064step1 permutation31 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw4065 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]

def raw4065step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]

def raw4065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical4065 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4065 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw4065 = injectiveMoment H raw4065step0 := by
      have hz : ∀ j, raw4065 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw4065step0 = (fun i j => raw4065 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4065 permutation104 hz
    injectiveMoment H raw4065step0 = injectiveMoment H raw4065step1 := by
      have heq : raw4065step1 = (fun i j => raw4065step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4065step0 permutation16 permutation5
    _ = injectiveMoment H node291 := by rfl

def raw4066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4066 = injectiveMoment H node2137 := by
  rfl

def raw4067 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4067 = injectiveMoment H node655 := by
  rfl

def raw4068 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4068 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4068 = injectiveMoment H node656 := by
  rfl

def raw4069 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical4069 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4069 = injectiveMoment H node657 := by
  rfl

def raw4070 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical4070 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4070 = injectiveMoment H node658 := by
  rfl

def raw4071 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4071 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4071 = injectiveMoment H node659 := by
  rfl

def raw4072 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw4072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical4072 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4072 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H raw4072 = injectiveMoment H raw4072step0 := by
      have heq : raw4072step0 = (fun i j => raw4072 (permutation60 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4072 permutation60 permutation5
    _ = injectiveMoment H node1291 := by rfl

def raw4073 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]

def raw4073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4073 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4073 = injectiveMoment H node659 := by
  calc
    injectiveMoment H raw4073 = injectiveMoment H raw4073step0 := by
      have heq : raw4073step0 = (fun i j => raw4073 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4073 permutation34 permutation3
    _ = injectiveMoment H node659 := by rfl

def raw4074 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]

def raw4074step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical4074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4074 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw4074 = injectiveMoment H raw4074step0 := by
      have heq : raw4074step0 = (fun i j => raw4074 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4074 permutation16 permutation5
    _ = injectiveMoment H node291 := by rfl

def raw4075 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]

def raw4075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4075 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4075 = injectiveMoment H node656 := by
  calc
    injectiveMoment H raw4075 = injectiveMoment H raw4075step0 := by
      have heq : raw4075step0 = (fun i j => raw4075 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4075 permutation35 permutation3
    _ = injectiveMoment H node656 := by rfl

def raw4076 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4076 = injectiveMoment H node660 := by
  rfl

def raw4077 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4077 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4077 = injectiveMoment H node661 := by
  rfl

def raw4078 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw4078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4078 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4078 = injectiveMoment H node661 := by
  calc
    injectiveMoment H raw4078 = injectiveMoment H raw4078step0 := by
      have heq : raw4078step0 = (fun i j => raw4078 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4078 permutation34 permutation3
    _ = injectiveMoment H node661 := by rfl

def raw4079 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4079 = injectiveMoment H node203 := by
  rfl

def raw4080 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical4080 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4080 = injectiveMoment H node662 := by
  rfl

def raw4081 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical4081 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4081 = injectiveMoment H node663 := by
  rfl

def raw4082 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical4082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4082 = injectiveMoment H node204 := by
  rfl

def raw4083 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

theorem canonical4083 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4083 = injectiveMoment H node664 := by
  rfl

def raw4084 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4084 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4084 = injectiveMoment H node665 := by
  rfl

def raw4085 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -2, 1]]

def raw4085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4085 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4085 = injectiveMoment H node665 := by
  calc
    injectiveMoment H raw4085 = injectiveMoment H raw4085step0 := by
      have heq : raw4085step0 = (fun i j => raw4085 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4085 permutation34 permutation3
    _ = injectiveMoment H node665 := by rfl

def raw4086 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -3, 2], ![1, 4, -5]]

theorem canonical4086 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4086 = injectiveMoment H node205 := by
  rfl

def raw4087 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical4087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4087 = injectiveMoment H node206 := by
  rfl

def raw4088 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw4088step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3]]

def raw4088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4088 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4088 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw4088 = injectiveMoment H raw4088step0 := by
      have heq : raw4088step0 = -raw4088 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4088).symm
    injectiveMoment H raw4088step0 = injectiveMoment H raw4088step1 := by
      have heq : raw4088step1 = (fun i j => raw4088step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4088step0 permutation28 permutation5
    _ = injectiveMoment H node185 := by rfl

def raw4089 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]

def raw4089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical4089 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4089 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw4089 = injectiveMoment H raw4089step0 := by
      have heq : raw4089step0 = -raw4089 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4089).symm
    injectiveMoment H raw4089step0 = injectiveMoment H raw4089step1 := by
      have heq : raw4089step1 = (fun i j => raw4089step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4089step0 permutation31 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw4090 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]

def raw4090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, -1, 2], ![-1, 0, 1]]

def raw4090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical4090 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4090 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw4090 = injectiveMoment H raw4090step0 := by
      have heq : raw4090step0 = -raw4090 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4090).symm
    injectiveMoment H raw4090step0 = injectiveMoment H raw4090step1 := by
      have heq : raw4090step1 = (fun i j => raw4090step0 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4090step0 permutation25 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw4091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]

def raw4091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]

def raw4091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]

def raw4091step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![2, 0, -2]]

def raw4091step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2]]

def raw4091step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical4091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4091 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw4091 = injectiveMoment H raw4091step0 := by
      have hz : ∀ j, raw4091 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw4091step0 = (fun i j => raw4091 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4091 permutation258 hz
    injectiveMoment H raw4091step0 = injectiveMoment H raw4091step1 := by
      have hz : ∀ j, raw4091step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw4091step1 = (fun i j => raw4091step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4091step0 permutation104 hz
    injectiveMoment H raw4091step1 = injectiveMoment H raw4091step2 := by
      have hz : ∀ j, raw4091step1 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw4091step2 = (fun i j => raw4091step1 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4091step1 permutation21 hz
    injectiveMoment H raw4091step2 = injectiveMoment H raw4091step3 := by
      have hz : ∀ j, raw4091step2 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw4091step3 = (fun i j => raw4091step2 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4091step2 permutation5 hz
    injectiveMoment H raw4091step3 = injectiveMoment H raw4091step4 := by
      have hz : ∀ i, raw4091step3 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw4091step4 = (fun i j => raw4091step3 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4091step3 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

def raw4092 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4092step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4092step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]

def raw4092step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical4092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4092 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw4092 = injectiveMoment H raw4092step0 := by
      have hz : ∀ j, raw4092 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4092step0 = (fun i j => raw4092 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4092 permutation80 hz
    injectiveMoment H raw4092step0 = injectiveMoment H raw4092step1 := by
      have hz : ∀ j, raw4092step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4092step1 = (fun i j => raw4092step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4092step0 permutation15 hz
    injectiveMoment H raw4092step1 = injectiveMoment H raw4092step2 := by
      have hz : ∀ i, raw4092step1 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw4092step2 = (fun i j => raw4092step1 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4092step1 permutation5 hz
    _ = injectiveMoment H node11 := by rfl

def raw4093 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4093step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical4093 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4093 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4093 = injectiveMoment H raw4093step0 := by
      have hz : ∀ j, raw4093 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw4093step0 = (fun i j => raw4093 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4093 permutation57 hz
    _ = injectiveMoment H node207 := by rfl

def raw4094 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4094 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4094 = injectiveMoment H raw4094step0 := by
      have hz : ∀ j, raw4094 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw4094step0 = (fun i j => raw4094 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4094 permutation57 hz
    _ = injectiveMoment H node210 := by rfl

def raw4095 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4095 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw4095 = injectiveMoment H raw4095step0 := by
      have hz : ∀ j, raw4095 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw4095step0 = (fun i j => raw4095 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4095 permutation57 hz
    injectiveMoment H raw4095step0 = injectiveMoment H raw4095step1 := by
      have heq : raw4095step1 = (fun i j => raw4095step0 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4095step0 permutation25 permutation6
    _ = injectiveMoment H node294 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
