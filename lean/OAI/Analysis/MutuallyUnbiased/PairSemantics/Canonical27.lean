import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw864 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]

def raw864step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw864 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw864 = injectiveMoment H raw864step0 := by
      have hz : ∀ j, raw864 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw864step0 = (fun i j => raw864 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw864 permutation104 hz
    _ = injectiveMoment H node24 := by rfl

def raw865 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]

def raw865step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw865 = injectiveMoment H node118 := by
  calc
    injectiveMoment H raw865 = injectiveMoment H raw865step0 := by
      have hz : ∀ j, raw865 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw865step0 = (fun i j => raw865 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw865 permutation258 hz
    _ = injectiveMoment H node118 := by rfl

def raw866 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical866 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw866 = injectiveMoment H node383 := by
  rfl

def raw867 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw867 = injectiveMoment H node118 := by
  rfl

def raw868 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]

def raw868step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical868 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw868 = injectiveMoment H node118 := by
  calc
    injectiveMoment H raw868 = injectiveMoment H raw868step0 := by
      have heq : raw868step0 = (fun i j => raw868 (permutation34 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw868 permutation34 permutation1
    _ = injectiveMoment H node118 := by rfl

def raw869 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical869 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw869 = injectiveMoment H node24 := by
  rfl

def raw870 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![0, 0], ![2, -2]]

def raw870step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

theorem canonical870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw870 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw870 = injectiveMoment H raw870step0 := by
      have hz : ∀ j, raw870 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw870step0 = (fun i j => raw870 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw870 permutation104 hz
    _ = injectiveMoment H node25 := by rfl

def raw871 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]

def raw871step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical871 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw871 = injectiveMoment H node118 := by
  calc
    injectiveMoment H raw871 = injectiveMoment H raw871step0 := by
      have heq : raw871step0 = (fun i j => raw871 (permutation36 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw871 permutation36 permutation1
    _ = injectiveMoment H node118 := by rfl

def raw872 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

theorem canonical872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw872 = injectiveMoment H node25 := by
  rfl

def raw873 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]

def raw873step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw873 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw873 = injectiveMoment H raw873step0 := by
      have heq : raw873step0 = (fun i j => raw873 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw873 permutation8 permutation2
    _ = injectiveMoment H node8 := by rfl

def raw874 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]

def raw874step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]

def raw874step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical874 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw874 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw874 = injectiveMoment H raw874step0 := by
      have hz : ∀ j, raw874 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw874step0 = (fun i j => raw874 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw874 permutation258 hz
    injectiveMoment H raw874step0 = injectiveMoment H raw874step1 := by
      have hz : ∀ j, raw874step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw874step1 = (fun i j => raw874step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw874step0 permutation57 hz
    _ = injectiveMoment H node24 := by rfl

def raw875 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw875step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical875 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw875 = injectiveMoment H node118 := by
  calc
    injectiveMoment H raw875 = injectiveMoment H raw875step0 := by
      have hz : ∀ j, raw875 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw875step0 = (fun i j => raw875 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw875 permutation202 hz
    _ = injectiveMoment H node118 := by rfl

def raw876 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]

def raw876step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical876 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw876 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw876 = injectiveMoment H raw876step0 := by
      have hz : ∀ j, raw876 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw876step0 = (fun i j => raw876 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw876 permutation57 hz
    _ = injectiveMoment H node24 := by rfl

def raw877 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]

def raw877step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

theorem canonical877 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw877 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw877 = injectiveMoment H raw877step0 := by
      have hz : ∀ j, raw877 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw877step0 = (fun i j => raw877 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw877 permutation57 hz
    _ = injectiveMoment H node25 := by rfl

def raw878 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]

def raw878step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]

def raw878step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]

def raw878step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw878step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical878 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw878 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw878 = injectiveMoment H raw878step0 := by
      have hz : ∀ j, raw878 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw878step0 = (fun i j => raw878 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw878 permutation258 hz
    injectiveMoment H raw878step0 = injectiveMoment H raw878step1 := by
      have hz : ∀ j, raw878step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw878step1 = (fun i j => raw878step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw878step0 permutation104 hz
    injectiveMoment H raw878step1 = injectiveMoment H raw878step2 := by
      have hz : ∀ j, raw878step1 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw878step2 = (fun i j => raw878step1 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw878step1 permutation21 hz
    injectiveMoment H raw878step2 = injectiveMoment H raw878step3 := by
      have hz : ∀ j, raw878step2 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw878step3 = (fun i j => raw878step2 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw878step2 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

def raw879 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw879step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw879step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw879step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical879 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw879 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw879 = injectiveMoment H raw879step0 := by
      have hz : ∀ j, raw879 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw879step0 = (fun i j => raw879 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw879 permutation241 hz
    injectiveMoment H raw879step0 = injectiveMoment H raw879step1 := by
      have hz : ∀ j, raw879step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw879step1 = (fun i j => raw879step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw879step0 permutation80 hz
    injectiveMoment H raw879step1 = injectiveMoment H raw879step2 := by
      have hz : ∀ j, raw879step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw879step2 = (fun i j => raw879step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw879step1 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

def raw880 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw880step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw880step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw880step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw880step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw880 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw880 = injectiveMoment H raw880step0 := by
      have hz : ∀ j, raw880 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw880step0 = (fun i j => raw880 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw880 permutation241 hz
    injectiveMoment H raw880step0 = injectiveMoment H raw880step1 := by
      have hz : ∀ j, raw880step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw880step1 = (fun i j => raw880step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw880step0 permutation80 hz
    injectiveMoment H raw880step1 = injectiveMoment H raw880step2 := by
      have hz : ∀ j, raw880step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw880step2 = (fun i j => raw880step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw880step1 permutation15 hz
    injectiveMoment H raw880step2 = injectiveMoment H raw880step3 := by
      have heq : raw880step3 = (fun i j => raw880step2 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw880step2 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw881 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]

def raw881step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]

def raw881step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw881step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw881 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw881 = injectiveMoment H raw881step0 := by
      have hz : ∀ j, raw881 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw881step0 = (fun i j => raw881 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw881 permutation104 hz
    injectiveMoment H raw881step0 = injectiveMoment H raw881step1 := by
      have hz : ∀ j, raw881step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw881step1 = (fun i j => raw881step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw881step0 permutation21 hz
    injectiveMoment H raw881step1 = injectiveMoment H raw881step2 := by
      have hz : ∀ j, raw881step1 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw881step2 = (fun i j => raw881step1 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw881step1 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

def raw882 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

def raw882step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw882step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw882step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical882 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw882 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw882 = injectiveMoment H raw882step0 := by
      have hz : ∀ j, raw882 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw882step0 = (fun i j => raw882 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw882 permutation258 hz
    injectiveMoment H raw882step0 = injectiveMoment H raw882step1 := by
      have hz : ∀ j, raw882step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw882step1 = (fun i j => raw882step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw882step0 permutation80 hz
    injectiveMoment H raw882step1 = injectiveMoment H raw882step2 := by
      have hz : ∀ j, raw882step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw882step2 = (fun i j => raw882step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw882step1 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

def raw883 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw883step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw883step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical883 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw883 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw883 = injectiveMoment H raw883step0 := by
      have hz : ∀ j, raw883 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw883step0 = (fun i j => raw883 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw883 permutation221 hz
    injectiveMoment H raw883step0 = injectiveMoment H raw883step1 := by
      have hz : ∀ j, raw883step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw883step1 = (fun i j => raw883step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw883step0 permutation57 hz
    _ = injectiveMoment H node26 := by rfl

def raw884 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw884step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw884step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical884 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw884 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw884 = injectiveMoment H raw884step0 := by
      have hz : ∀ j, raw884 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw884step0 = (fun i j => raw884 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw884 permutation80 hz
    injectiveMoment H raw884step0 = injectiveMoment H raw884step1 := by
      have hz : ∀ j, raw884step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw884step1 = (fun i j => raw884step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw884step0 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

def raw885 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]

def raw885step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw885step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw885step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw885 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw885 = injectiveMoment H raw885step0 := by
      have hz : ∀ j, raw885 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw885step0 = (fun i j => raw885 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw885 permutation308 hz
    injectiveMoment H raw885step0 = injectiveMoment H raw885step1 := by
      have hz : ∀ j, raw885step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw885step1 = (fun i j => raw885step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw885step0 permutation80 hz
    injectiveMoment H raw885step1 = injectiveMoment H raw885step2 := by
      have hz : ∀ j, raw885step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw885step2 = (fun i j => raw885step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw885step1 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

def raw886 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw886step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw886step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw886step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical886 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw886 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw886 = injectiveMoment H raw886step0 := by
      have hz : ∀ j, raw886 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw886step0 = (fun i j => raw886 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw886 permutation80 hz
    injectiveMoment H raw886step0 = injectiveMoment H raw886step1 := by
      have hz : ∀ j, raw886step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw886step1 = (fun i j => raw886step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw886step0 permutation15 hz
    injectiveMoment H raw886step1 = injectiveMoment H raw886step2 := by
      have heq : raw886step2 = (fun i j => raw886step1 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw886step1 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw887 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]

def raw887step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw887step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical887 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw887 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw887 = injectiveMoment H raw887step0 := by
      have hz : ∀ j, raw887 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw887step0 = (fun i j => raw887 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw887 permutation21 hz
    injectiveMoment H raw887step0 = injectiveMoment H raw887step1 := by
      have hz : ∀ j, raw887step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw887step1 = (fun i j => raw887step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw887step0 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

def raw888 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![-1, 1], ![3, -3]]

def raw888step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]

def raw888step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical888 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw888 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw888 = injectiveMoment H raw888step0 := by
      have hz : ∀ j, raw888 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw888step0 = (fun i j => raw888 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw888 permutation57 hz
    injectiveMoment H raw888step0 = injectiveMoment H raw888step1 := by
      have heq : raw888step1 = (fun i j => raw888step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw888step0 permutation11 permutation1
    _ = injectiveMoment H node24 := by rfl

def raw889 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw889step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

def raw889step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw889step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical889 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw889 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw889 = injectiveMoment H raw889step0 := by
      have hz : ∀ j, raw889 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw889step0 = (fun i j => raw889 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw889 permutation258 hz
    injectiveMoment H raw889step0 = injectiveMoment H raw889step1 := by
      have hz : ∀ j, raw889step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw889step1 = (fun i j => raw889step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw889step0 permutation104 hz
    injectiveMoment H raw889step1 = injectiveMoment H raw889step2 := by
      have hz : ∀ j, raw889step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw889step2 = (fun i j => raw889step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw889step1 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

def raw890 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw890step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw890step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical890 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw890 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw890 = injectiveMoment H raw890step0 := by
      have hz : ∀ j, raw890 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw890step0 = (fun i j => raw890 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw890 permutation241 hz
    injectiveMoment H raw890step0 = injectiveMoment H raw890step1 := by
      have hz : ∀ j, raw890step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw890step1 = (fun i j => raw890step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw890step0 permutation57 hz
    _ = injectiveMoment H node26 := by rfl

def raw891 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

def raw891step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw891step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw891 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw891 = injectiveMoment H raw891step0 := by
      have hz : ∀ j, raw891 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw891step0 = (fun i j => raw891 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw891 permutation104 hz
    injectiveMoment H raw891step0 = injectiveMoment H raw891step1 := by
      have hz : ∀ j, raw891step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw891step1 = (fun i j => raw891step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw891step0 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

def raw892 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw892step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw892step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw892 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw892 = injectiveMoment H raw892step0 := by
      have hz : ∀ j, raw892 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw892step0 = (fun i j => raw892 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw892 permutation258 hz
    injectiveMoment H raw892step0 = injectiveMoment H raw892step1 := by
      have hz : ∀ j, raw892step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw892step1 = (fun i j => raw892step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw892step0 permutation57 hz
    _ = injectiveMoment H node26 := by rfl

def raw893 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw893step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw893 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw893 = injectiveMoment H raw893step0 := by
      have hz : ∀ j, raw893 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw893step0 = (fun i j => raw893 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw893 permutation57 hz
    _ = injectiveMoment H node26 := by rfl

def raw894 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw894step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw894step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical894 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw894 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw894 = injectiveMoment H raw894step0 := by
      have hz : ∀ j, raw894 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw894step0 = (fun i j => raw894 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw894 permutation308 hz
    injectiveMoment H raw894step0 = injectiveMoment H raw894step1 := by
      have hz : ∀ j, raw894step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw894step1 = (fun i j => raw894step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw894step0 permutation57 hz
    _ = injectiveMoment H node26 := by rfl

def raw895 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw895step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
