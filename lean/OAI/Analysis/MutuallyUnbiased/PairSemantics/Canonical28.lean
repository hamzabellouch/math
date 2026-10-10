import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw896 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]

def raw896step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw896step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical896 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw896 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw896 = injectiveMoment H raw896step0 := by
      have hz : ∀ j, raw896 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw896step0 = (fun i j => raw896 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw896 permutation128 hz
    injectiveMoment H raw896step0 = injectiveMoment H raw896step1 := by
      have hz : ∀ j, raw896step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw896step1 = (fun i j => raw896step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw896step0 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

def raw897 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]

def raw897step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw897step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw897step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical897 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw897 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw897 = injectiveMoment H raw897step0 := by
      have hz : ∀ j, raw897 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw897step0 = (fun i j => raw897 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw897 permutation104 hz
    injectiveMoment H raw897step0 = injectiveMoment H raw897step1 := by
      have hz : ∀ j, raw897step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw897step1 = (fun i j => raw897step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw897step0 permutation15 hz
    injectiveMoment H raw897step1 = injectiveMoment H raw897step2 := by
      have heq : raw897step2 = (fun i j => raw897step1 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw897step1 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw898 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw898step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw898step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical898 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw898 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw898 = injectiveMoment H raw898step0 := by
      have hz : ∀ j, raw898 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw898step0 = (fun i j => raw898 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw898 permutation15 hz
    injectiveMoment H raw898step0 = injectiveMoment H raw898step1 := by
      have heq : raw898step1 = (fun i j => raw898step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw898step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw899 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1], ![0, 0]]

def raw899step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw899step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw899step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical899 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw899 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw899 = injectiveMoment H raw899step0 := by
      have hz : ∀ j, raw899 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw899step0 = (fun i j => raw899 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw899 permutation128 hz
    injectiveMoment H raw899step0 = injectiveMoment H raw899step1 := by
      have hz : ∀ j, raw899step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw899step1 = (fun i j => raw899step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw899step0 permutation15 hz
    injectiveMoment H raw899step1 = injectiveMoment H raw899step2 := by
      have heq : raw899step2 = (fun i j => raw899step1 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw899step1 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw900 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw900step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

def raw901 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![0, 0]]

def raw901step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw901step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical901 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw901 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw901 = injectiveMoment H raw901step0 := by
      have hz : ∀ j, raw901 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw901step0 = (fun i j => raw901 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw901 permutation27 hz
    injectiveMoment H raw901step0 = injectiveMoment H raw901step1 := by
      have hz : ∀ j, raw901step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw901step1 = (fun i j => raw901step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw901step0 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

def raw902 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]

def raw902step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical902 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw902 = injectiveMoment H node118 := by
  calc
    injectiveMoment H raw902 = injectiveMoment H raw902step0 := by
      have heq : raw902step0 = (fun i j => raw902 (permutation39 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw902 permutation39 permutation1
    _ = injectiveMoment H node118 := by rfl

def raw903 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]

def raw903step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical903 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw903 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw903 = injectiveMoment H raw903step0 := by
      have heq : raw903step0 = (fun i j => raw903 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw903 permutation11 permutation1
    _ = injectiveMoment H node24 := by rfl

def raw904 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw904step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw904step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw904step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical904 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw904 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw904 = injectiveMoment H raw904step0 := by
      have hz : ∀ j, raw904 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw904step0 = (fun i j => raw904 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw904 permutation258 hz
    injectiveMoment H raw904step0 = injectiveMoment H raw904step1 := by
      have hz : ∀ j, raw904step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw904step1 = (fun i j => raw904step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw904step0 permutation104 hz
    injectiveMoment H raw904step1 = injectiveMoment H raw904step2 := by
      have hz : ∀ j, raw904step1 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw904step2 = (fun i j => raw904step1 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw904step1 permutation21 hz
    _ = injectiveMoment H node10 := by rfl

def raw905 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw905step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw905step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical905 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw905 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw905 = injectiveMoment H raw905step0 := by
      have hz : ∀ j, raw905 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw905step0 = (fun i j => raw905 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw905 permutation241 hz
    injectiveMoment H raw905step0 = injectiveMoment H raw905step1 := by
      have hz : ∀ j, raw905step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw905step1 = (fun i j => raw905step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw905step0 permutation80 hz
    _ = injectiveMoment H node26 := by rfl

def raw906 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw906step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw906step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical906 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw906 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw906 = injectiveMoment H raw906step0 := by
      have hz : ∀ j, raw906 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw906step0 = (fun i j => raw906 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw906 permutation104 hz
    injectiveMoment H raw906step0 = injectiveMoment H raw906step1 := by
      have hz : ∀ j, raw906step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw906step1 = (fun i j => raw906step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw906step0 permutation21 hz
    _ = injectiveMoment H node10 := by rfl

def raw907 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw907step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical907 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw907 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw907 = injectiveMoment H raw907step0 := by
      have hz : ∀ j, raw907 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw907step0 = (fun i j => raw907 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw907 permutation80 hz
    _ = injectiveMoment H node26 := by rfl

def raw908 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def raw908step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw908step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical908 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw908 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw908 = injectiveMoment H raw908step0 := by
      have hz : ∀ j, raw908 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw908step0 = (fun i j => raw908 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw908 permutation308 hz
    injectiveMoment H raw908step0 = injectiveMoment H raw908step1 := by
      have hz : ∀ j, raw908step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw908step1 = (fun i j => raw908step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw908step0 permutation80 hz
    _ = injectiveMoment H node26 := by rfl

def raw909 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw909step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw909 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw909 = injectiveMoment H raw909step0 := by
      have hz : ∀ j, raw909 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw909step0 = (fun i j => raw909 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw909 permutation21 hz
    _ = injectiveMoment H node10 := by rfl

def raw910 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]

def raw910step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw910step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical910 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw910 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw910 = injectiveMoment H raw910step0 := by
      have hz : ∀ j, raw910 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw910step0 = (fun i j => raw910 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw910 permutation128 hz
    injectiveMoment H raw910step0 = injectiveMoment H raw910step1 := by
      have hz : ∀ j, raw910step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw910step1 = (fun i j => raw910step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw910step0 permutation21 hz
    _ = injectiveMoment H node10 := by rfl

def raw911 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw911step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw911step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical911 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw911 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw911 = injectiveMoment H raw911step0 := by
      have hz : ∀ j, raw911 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw911step0 = (fun i j => raw911 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw911 permutation258 hz
    injectiveMoment H raw911step0 = injectiveMoment H raw911step1 := by
      have hz : ∀ j, raw911step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw911step1 = (fun i j => raw911step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw911step0 permutation104 hz
    _ = injectiveMoment H node26 := by rfl

def raw912 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw912step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical912 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw912 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw912 = injectiveMoment H raw912step0 := by
      have hz : ∀ j, raw912 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw912step0 = (fun i j => raw912 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw912 permutation104 hz
    _ = injectiveMoment H node26 := by rfl

def raw913 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]

def raw913step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw913step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical913 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw913 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw913 = injectiveMoment H raw913step0 := by
      have hz : ∀ j, raw913 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw913step0 = (fun i j => raw913 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw913 permutation308 hz
    injectiveMoment H raw913step0 = injectiveMoment H raw913step1 := by
      have hz : ∀ j, raw913step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw913step1 = (fun i j => raw913step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw913step0 permutation104 hz
    _ = injectiveMoment H node26 := by rfl

def raw914 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw914 = injectiveMoment H node26 := by
  rfl

def raw915 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw915step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical915 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw915 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw915 = injectiveMoment H raw915step0 := by
      have hz : ∀ j, raw915 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw915step0 = (fun i j => raw915 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw915 permutation128 hz
    _ = injectiveMoment H node26 := by rfl

def raw916 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw916step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw916step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical916 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw916 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw916 = injectiveMoment H raw916step0 := by
      have hz : ∀ j, raw916 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw916step0 = (fun i j => raw916 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw916 permutation308 hz
    injectiveMoment H raw916step0 = injectiveMoment H raw916step1 := by
      have hz : ∀ j, raw916step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw916step1 = (fun i j => raw916step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw916step0 permutation128 hz
    _ = injectiveMoment H node26 := by rfl

def raw917 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

def raw918 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![0, 0]]

def raw918step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw918 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw918 = injectiveMoment H raw918step0 := by
      have hz : ∀ j, raw918 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw918step0 = (fun i j => raw918 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw918 permutation27 hz
    _ = injectiveMoment H node10 := by rfl

def raw919 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![0, 0], ![0, 0]]

def raw919step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![0, 0]]

def raw919step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical919 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw919 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw919 = injectiveMoment H raw919step0 := by
      have hz : ∀ j, raw919 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw919step0 = (fun i j => raw919 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw919 permutation128 hz
    injectiveMoment H raw919step0 = injectiveMoment H raw919step1 := by
      have hz : ∀ j, raw919step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw919step1 = (fun i j => raw919step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw919step0 permutation27 hz
    _ = injectiveMoment H node10 := by rfl

def raw920 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![1, -1]]

def raw920step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]

def raw920step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]

def raw920step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw920step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical920 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw920 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw920 = injectiveMoment H raw920step0 := by
      have hz : ∀ j, raw920 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw920step0 = (fun i j => raw920 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw920 permutation258 hz
    injectiveMoment H raw920step0 = injectiveMoment H raw920step1 := by
      have hz : ∀ j, raw920step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw920step1 = (fun i j => raw920step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw920step0 permutation104 hz
    injectiveMoment H raw920step1 = injectiveMoment H raw920step2 := by
      have hz : ∀ j, raw920step1 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw920step2 = (fun i j => raw920step1 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw920step1 permutation21 hz
    injectiveMoment H raw920step2 = injectiveMoment H raw920step3 := by
      have heq : raw920step3 = (fun i j => raw920step2 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw920step2 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw921 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]

def raw921step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]

def raw921step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw921step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical921 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw921 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw921 = injectiveMoment H raw921step0 := by
      have hz : ∀ j, raw921 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw921step0 = (fun i j => raw921 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw921 permutation104 hz
    injectiveMoment H raw921step0 = injectiveMoment H raw921step1 := by
      have hz : ∀ j, raw921step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw921step1 = (fun i j => raw921step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw921step0 permutation21 hz
    injectiveMoment H raw921step1 = injectiveMoment H raw921step2 := by
      have heq : raw921step2 = (fun i j => raw921step1 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw921step1 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw922 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]

def raw922step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw922step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw922 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw922 = injectiveMoment H raw922step0 := by
      have hz : ∀ j, raw922 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw922step0 = (fun i j => raw922 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw922 permutation21 hz
    injectiveMoment H raw922step0 = injectiveMoment H raw922step1 := by
      have heq : raw922step1 = (fun i j => raw922step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw922step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw923 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1], ![0, 0]]

def raw923step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]

def raw923step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw923step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw923 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw923 = injectiveMoment H raw923step0 := by
      have hz : ∀ j, raw923 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw923step0 = (fun i j => raw923 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw923 permutation128 hz
    injectiveMoment H raw923step0 = injectiveMoment H raw923step1 := by
      have hz : ∀ j, raw923step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw923step1 = (fun i j => raw923step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw923step0 permutation21 hz
    injectiveMoment H raw923step1 = injectiveMoment H raw923step2 := by
      have heq : raw923step2 = (fun i j => raw923step1 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw923step1 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw924 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw924step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw925 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![0, 0]]

def raw925step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw925step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw925 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw925 = injectiveMoment H raw925step0 := by
      have hz : ∀ j, raw925 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw925step0 = (fun i j => raw925 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw925 permutation27 hz
    injectiveMoment H raw925step0 = injectiveMoment H raw925step1 := by
      have heq : raw925step1 = (fun i j => raw925step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw925step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw926 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

def raw927 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![3, -3], ![0, 0]]

def raw927step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical927 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw927 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw927 = injectiveMoment H raw927step0 := by
      have hz : ∀ j, raw927 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw927step0 = (fun i j => raw927 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw927 permutation7 hz
    _ = injectiveMoment H node3 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
