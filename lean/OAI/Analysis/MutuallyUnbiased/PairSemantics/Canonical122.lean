import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3904 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw3904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw3904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3904 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3904 = injectiveMoment H node322 := by
  calc
    injectiveMoment H raw3904 = injectiveMoment H raw3904step0 := by
      have heq : raw3904step0 = -raw3904 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3904).symm
    injectiveMoment H raw3904step0 = injectiveMoment H raw3904step1 := by
      have heq : raw3904step1 = (fun i j => raw3904step0 (permutation131 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3904step0 permutation131 permutation5
    _ = injectiveMoment H node322 := by rfl

def raw3905 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -1, 2], ![-1, 1, 0], ![-1, -1, 2]]

def raw3905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3905 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3905 = injectiveMoment H node1131 := by
  calc
    injectiveMoment H raw3905 = injectiveMoment H raw3905step0 := by
      have heq : raw3905step0 = -raw3905 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3905).symm
    injectiveMoment H raw3905step0 = injectiveMoment H raw3905step1 := by
      have heq : raw3905step1 = (fun i j => raw3905step0 (permutation99 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3905step0 permutation99 permutation5
    _ = injectiveMoment H node1131 := by rfl

def raw3906 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 2, -3], ![2, -1, -1]]

def raw3906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -2, 3], ![-2, 1, 1]]

def raw3906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3906 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3906 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw3906 = injectiveMoment H raw3906step0 := by
      have heq : raw3906step0 = -raw3906 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3906).symm
    injectiveMoment H raw3906step0 = injectiveMoment H raw3906step1 := by
      have heq : raw3906step1 = (fun i j => raw3906step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3906step0 permutation22 permutation5
    _ = injectiveMoment H node184 := by rfl

def raw3907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]

def raw3907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -3, 4], ![-2, 2, 0]]

def raw3907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical3907 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3907 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw3907 = injectiveMoment H raw3907step0 := by
      have heq : raw3907step0 = -raw3907 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3907).symm
    injectiveMoment H raw3907step0 = injectiveMoment H raw3907step1 := by
      have heq : raw3907step1 = (fun i j => raw3907step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3907step0 permutation21 permutation5
    _ = injectiveMoment H node85 := by rfl

def raw3908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw3908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3908 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3908 = injectiveMoment H node2652 := by
  calc
    injectiveMoment H raw3908 = injectiveMoment H raw3908step0 := by
      have heq : raw3908step0 = (fun i j => raw3908 (permutation299 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3908 permutation299 permutation6
    _ = injectiveMoment H node2652 := by rfl

def raw3909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw3909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical3909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3909 = injectiveMoment H node2661 := by
  calc
    injectiveMoment H raw3909 = injectiveMoment H raw3909step0 := by
      have heq : raw3909step0 = (fun i j => raw3909 (permutation378 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3909 permutation378 permutation6
    _ = injectiveMoment H node2661 := by rfl

def raw3910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical3910 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3910 = injectiveMoment H node2138 := by
  calc
    injectiveMoment H raw3910 = injectiveMoment H raw3910step0 := by
      have heq : raw3910step0 = (fun i j => raw3910 (permutation378 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3910 permutation378 permutation6
    _ = injectiveMoment H node2138 := by rfl

def raw3911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw3911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical3911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3911 = injectiveMoment H node2300 := by
  calc
    injectiveMoment H raw3911 = injectiveMoment H raw3911step0 := by
      have heq : raw3911step0 = -raw3911 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3911).symm
    injectiveMoment H raw3911step0 = injectiveMoment H raw3911step1 := by
      have heq : raw3911step1 = (fun i j => raw3911step0 (permutation224 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3911step0 permutation224 permutation6
    _ = injectiveMoment H node2300 := by rfl

def raw3912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw3912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical3912 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3912 = injectiveMoment H node2299 := by
  calc
    injectiveMoment H raw3912 = injectiveMoment H raw3912step0 := by
      have heq : raw3912step0 = -raw3912 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3912).symm
    injectiveMoment H raw3912step0 = injectiveMoment H raw3912step1 := by
      have heq : raw3912step1 = (fun i j => raw3912step0 (permutation222 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3912step0 permutation222 permutation6
    _ = injectiveMoment H node2299 := by rfl

def raw3913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw3913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical3913 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3913 = injectiveMoment H node2093 := by
  calc
    injectiveMoment H raw3913 = injectiveMoment H raw3913step0 := by
      have heq : raw3913step0 = (fun i j => raw3913 (permutation378 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3913 permutation378 permutation6
    _ = injectiveMoment H node2093 := by rfl

def raw3914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical3914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3914 = injectiveMoment H node2126 := by
  calc
    injectiveMoment H raw3914 = injectiveMoment H raw3914step0 := by
      have heq : raw3914step0 = (fun i j => raw3914 (permutation391 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3914 permutation391 permutation6
    _ = injectiveMoment H node2126 := by rfl

def raw3915 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]

def raw3915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw3915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical3915 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3915 = injectiveMoment H node703 := by
  calc
    injectiveMoment H raw3915 = injectiveMoment H raw3915step0 := by
      have heq : raw3915step0 = -raw3915 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3915).symm
    injectiveMoment H raw3915step0 = injectiveMoment H raw3915step1 := by
      have heq : raw3915step1 = (fun i j => raw3915step0 (permutation80 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3915step0 permutation80 permutation6
    _ = injectiveMoment H node703 := by rfl

def raw3916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def raw3916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -3, 5]]

def raw3916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem canonical3916 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3916 = injectiveMoment H node1382 := by
  calc
    injectiveMoment H raw3916 = injectiveMoment H raw3916step0 := by
      have heq : raw3916step0 = -raw3916 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3916).symm
    injectiveMoment H raw3916step0 = injectiveMoment H raw3916step1 := by
      have heq : raw3916step1 = (fun i j => raw3916step0 (permutation335 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3916step0 permutation335 permutation5
    _ = injectiveMoment H node1382 := by rfl

def raw3917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw3917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw3917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3917 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3917 = injectiveMoment H node1391 := by
  calc
    injectiveMoment H raw3917 = injectiveMoment H raw3917step0 := by
      have heq : raw3917step0 = -raw3917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3917).symm
    injectiveMoment H raw3917step0 = injectiveMoment H raw3917step1 := by
      have heq : raw3917step1 = (fun i j => raw3917step0 (permutation334 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3917step0 permutation334 permutation5
    _ = injectiveMoment H node1391 := by rfl

def raw3918 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]

def raw3918step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]

def raw3918step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical3918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3918 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw3918 = injectiveMoment H raw3918step0 := by
      have hz : ∀ j, raw3918 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3918step0 = (fun i j => raw3918 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3918 permutation80 hz
    injectiveMoment H raw3918step0 = injectiveMoment H raw3918step1 := by
      have hz : ∀ i, raw3918step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw3918step1 = (fun i j => raw3918step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3918step0 permutation5 hz
    _ = injectiveMoment H node46 := by rfl

def raw3919 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]

def raw3919step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical3919 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3919 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw3919 = injectiveMoment H raw3919step0 := by
      have hz : ∀ j, raw3919 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3919step0 = (fun i j => raw3919 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3919 permutation80 hz
    injectiveMoment H raw3919step0 = injectiveMoment H raw3919step1 := by
      have heq : raw3919step1 = (fun i j => raw3919step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3919step0 permutation29 permutation6
    _ = injectiveMoment H node288 := by rfl

def raw3920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw3920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical3920 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3920 = injectiveMoment H node2662 := by
  calc
    injectiveMoment H raw3920 = injectiveMoment H raw3920step0 := by
      have heq : raw3920step0 = (fun i j => raw3920 (permutation398 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3920 permutation398 permutation6
    _ = injectiveMoment H node2662 := by rfl

def raw3921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical3921 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3921 = injectiveMoment H node2139 := by
  calc
    injectiveMoment H raw3921 = injectiveMoment H raw3921step0 := by
      have heq : raw3921step0 = (fun i j => raw3921 (permutation398 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3921 permutation398 permutation6
    _ = injectiveMoment H node2139 := by rfl

def raw3922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

theorem canonical3922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3922 = injectiveMoment H node2094 := by
  rfl

def raw3923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw3923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical3923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3923 = injectiveMoment H node2801 := by
  calc
    injectiveMoment H raw3923 = injectiveMoment H raw3923step0 := by
      have heq : raw3923step0 = (fun i j => raw3923 (permutation254 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3923 permutation254 permutation6
    _ = injectiveMoment H node2801 := by rfl

def raw3924 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw3924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical3924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3924 = injectiveMoment H node1292 := by
  calc
    injectiveMoment H raw3924 = injectiveMoment H raw3924step0 := by
      have heq : raw3924step0 = (fun i j => raw3924 (permutation124 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3924 permutation124 permutation6
    _ = injectiveMoment H node1292 := by rfl

def raw3925 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw3925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical3925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3925 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H raw3925 = injectiveMoment H raw3925step0 := by
      have heq : raw3925step0 = (fun i j => raw3925 (permutation147 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3925 permutation147 permutation6
    _ = injectiveMoment H node1152 := by rfl

def raw3926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

theorem canonical3926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3926 = injectiveMoment H node670 := by
  calc
    injectiveMoment H raw3926 = injectiveMoment H raw3926step0 := by
      have heq : raw3926step0 = (fun i j => raw3926 (permutation134 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3926 permutation134 permutation6
    _ = injectiveMoment H node670 := by rfl

def raw3927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw3927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw3927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical3927 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3927 = injectiveMoment H node642 := by
  calc
    injectiveMoment H raw3927 = injectiveMoment H raw3927step0 := by
      have heq : raw3927step0 = -raw3927 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3927).symm
    injectiveMoment H raw3927step0 = injectiveMoment H raw3927step1 := by
      have heq : raw3927step1 = (fun i j => raw3927step0 (permutation100 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3927step0 permutation100 permutation5
    _ = injectiveMoment H node642 := by rfl

def raw3928 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw3928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical3928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3928 = injectiveMoment H node656 := by
  calc
    injectiveMoment H raw3928 = injectiveMoment H raw3928step0 := by
      have heq : raw3928step0 = (fun i j => raw3928 (permutation147 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3928 permutation147 permutation6
    _ = injectiveMoment H node656 := by rfl

def raw3929 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw3929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw3929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical3929 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3929 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H raw3929 = injectiveMoment H raw3929step0 := by
      have heq : raw3929step0 = -raw3929 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3929).symm
    injectiveMoment H raw3929step0 = injectiveMoment H raw3929step1 := by
      have heq : raw3929step1 = (fun i j => raw3929step0 (permutation147 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3929step0 permutation147 permutation5
    _ = injectiveMoment H node1152 := by rfl

def raw3930 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw3930step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical3930 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3930 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw3930 = injectiveMoment H raw3930step0 := by
      have hz : ∀ i, raw3930 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw3930step0 = (fun i j => raw3930 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3930 permutation5 hz
    _ = injectiveMoment H node232 := by rfl

def raw3931 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3931step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical3931 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3931 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw3931 = injectiveMoment H raw3931step0 := by
      have heq : raw3931step0 = (fun i j => raw3931 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3931 permutation29 permutation6
    _ = injectiveMoment H node288 := by rfl

def raw3932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw3932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical3932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3932 = injectiveMoment H node2102 := by
  calc
    injectiveMoment H raw3932 = injectiveMoment H raw3932step0 := by
      have heq : raw3932step0 = -raw3932 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3932).symm
    injectiveMoment H raw3932step0 = injectiveMoment H raw3932step1 := by
      have heq : raw3932step1 = (fun i j => raw3932step0 (permutation177 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3932step0 permutation177 permutation8
    _ = injectiveMoment H node2102 := by rfl

def raw3933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical3933 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3933 = injectiveMoment H node2125 := by
  calc
    injectiveMoment H raw3933 = injectiveMoment H raw3933step0 := by
      have heq : raw3933step0 = (fun i j => raw3933 (permutation392 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3933 permutation392 permutation8
    _ = injectiveMoment H node2125 := by rfl

def raw3934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw3934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical3934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3934 = injectiveMoment H node2129 := by
  calc
    injectiveMoment H raw3934 = injectiveMoment H raw3934step0 := by
      have heq : raw3934step0 = -raw3934 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3934).symm
    injectiveMoment H raw3934step0 = injectiveMoment H raw3934step1 := by
      have heq : raw3934step1 = (fun i j => raw3934step0 (permutation151 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3934step0 permutation151 permutation8
    _ = injectiveMoment H node2129 := by rfl

def raw3935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical3935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3935 = injectiveMoment H node2131 := by
  calc
    injectiveMoment H raw3935 = injectiveMoment H raw3935step0 := by
      have heq : raw3935step0 = (fun i j => raw3935 (permutation389 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3935 permutation389 permutation6
    _ = injectiveMoment H node2131 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
