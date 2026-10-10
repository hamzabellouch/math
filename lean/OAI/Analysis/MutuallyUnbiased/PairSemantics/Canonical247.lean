import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7904 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, -2, 1, 3], ![3, 1, -2, -2]]

def raw7904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![1, 1, -2], ![-1, 3, -2]]

def raw7904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7904 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7904 = injectiveMoment H node262 := by
  calc
    injectiveMoment H raw7904 = injectiveMoment H raw7904step0 := by
      have heq : raw7904step0 = raw7904.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7904).symm
    injectiveMoment H raw7904step0 = injectiveMoment H raw7904step1 := by
      have heq : raw7904step1 = (fun i j => raw7904step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7904step0 permutation13 permutation3
    _ = injectiveMoment H node262 := by rfl

def raw7905 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, -2, 2, 2], ![3, 1, -3, -1]]

def raw7905step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![1, 2, -3], ![-1, 2, -1]]

def raw7905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical7905 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7905 = injectiveMoment H node260 := by
  calc
    injectiveMoment H raw7905 = injectiveMoment H raw7905step0 := by
      have heq : raw7905step0 = raw7905.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7905).symm
    injectiveMoment H raw7905step0 = injectiveMoment H raw7905step1 := by
      have heq : raw7905step1 = (fun i j => raw7905step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7905step0 permutation13 permutation3
    _ = injectiveMoment H node260 := by rfl

def raw7906 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, -2, 3, 1], ![3, 1, -4, 0]]

def raw7906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![1, 3, -4], ![-1, 1, 0]]

def raw7906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, -3, 4], ![1, -1, 0]]

def raw7906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7906 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7906 = injectiveMoment H node245 := by
  calc
    injectiveMoment H raw7906 = injectiveMoment H raw7906step0 := by
      have heq : raw7906step0 = raw7906.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7906).symm
    injectiveMoment H raw7906step0 = injectiveMoment H raw7906step1 := by
      have heq : raw7906step1 = -raw7906step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7906step0).symm
    injectiveMoment H raw7906step1 = injectiveMoment H raw7906step2 := by
      have heq : raw7906step2 = (fun i j => raw7906step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7906step1 permutation24 permutation3
    _ = injectiveMoment H node245 := by rfl

def raw7907 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, 1, 1, 0], ![3, -2, -2, 1]]

def raw7907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 1, -2], ![1, 1, -2], ![-1, 0, 1]]

def raw7907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7907 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7907 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw7907 = injectiveMoment H raw7907step0 := by
      have heq : raw7907step0 = raw7907.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7907).symm
    injectiveMoment H raw7907step0 = injectiveMoment H raw7907step1 := by
      have heq : raw7907step1 = (fun i j => raw7907step0 (permutation13 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7907step0 permutation13 permutation5
    _ = injectiveMoment H node175 := by rfl

def raw7908 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, 1, 2, -1], ![3, -2, -3, 2]]

def raw7908step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 1, -2], ![1, 2, -3], ![-1, -1, 2]]

def raw7908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical7908 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7908 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw7908 = injectiveMoment H raw7908step0 := by
      have heq : raw7908step0 = raw7908.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7908).symm
    injectiveMoment H raw7908step0 = injectiveMoment H raw7908step1 := by
      have heq : raw7908step1 = (fun i j => raw7908step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7908step0 permutation13 permutation3
    _ = injectiveMoment H node258 := by rfl

def raw7909 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -3, 1, 3], ![2, 2, -2, -2]]

def raw7909step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![1, 1, -2], ![-1, 3, -2]]

def raw7909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical7909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7909 = injectiveMoment H node260 := by
  calc
    injectiveMoment H raw7909 = injectiveMoment H raw7909step0 := by
      have heq : raw7909step0 = raw7909.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7909).symm
    injectiveMoment H raw7909step0 = injectiveMoment H raw7909step1 := by
      have heq : raw7909step1 = (fun i j => raw7909step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7909step0 permutation28 permutation4
    _ = injectiveMoment H node260 := by rfl

def raw7910 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -3, 2, 2], ![2, 2, -3, -1]]

def raw7910step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![1, 2, -3], ![-1, 2, -1]]

def raw7910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, -2, 3], ![1, -2, 1]]

def raw7910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7910 = injectiveMoment H node262 := by
  calc
    injectiveMoment H raw7910 = injectiveMoment H raw7910step0 := by
      have heq : raw7910step0 = raw7910.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7910).symm
    injectiveMoment H raw7910step0 = injectiveMoment H raw7910step1 := by
      have heq : raw7910step1 = -raw7910step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7910step0).symm
    injectiveMoment H raw7910step1 = injectiveMoment H raw7910step2 := by
      have heq : raw7910step2 = (fun i j => raw7910step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7910step1 permutation24 permutation3
    _ = injectiveMoment H node262 := by rfl

def raw7911 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -3, 3, 1], ![2, 2, -4, 0]]

def raw7911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![1, 3, -4], ![-1, 1, 0]]

def raw7911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, -3, 4], ![1, -1, 0]]

def raw7911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7911 = injectiveMoment H node247 := by
  calc
    injectiveMoment H raw7911 = injectiveMoment H raw7911step0 := by
      have heq : raw7911step0 = raw7911.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7911).symm
    injectiveMoment H raw7911step0 = injectiveMoment H raw7911step1 := by
      have heq : raw7911step1 = -raw7911step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7911step0).symm
    injectiveMoment H raw7911step1 = injectiveMoment H raw7911step2 := by
      have heq : raw7911step2 = (fun i j => raw7911step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7911step1 permutation24 permutation3
    _ = injectiveMoment H node247 := by rfl

def raw7912 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, -2, 5], ![2, 1, 1, -4]]

def raw7912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, -2, 1], ![-1, 5, -4]]

def raw7912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7912 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7912 = injectiveMoment H node234 := by
  calc
    injectiveMoment H raw7912 = injectiveMoment H raw7912step0 := by
      have heq : raw7912step0 = raw7912.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7912).symm
    injectiveMoment H raw7912step0 = injectiveMoment H raw7912step1 := by
      have heq : raw7912step1 = (fun i j => raw7912step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7912step0 permutation27 permutation4
    _ = injectiveMoment H node234 := by rfl

def raw7913 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, 1, 2], ![2, 1, -2, -1]]

def raw7913step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![-1, 2, -1]]

def raw7913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7913 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7913 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw7913 = injectiveMoment H raw7913step0 := by
      have heq : raw7913step0 = raw7913.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7913).symm
    injectiveMoment H raw7913step0 = injectiveMoment H raw7913step1 := by
      have heq : raw7913step1 = (fun i j => raw7913step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7913step0 permutation13 permutation3
    _ = injectiveMoment H node276 := by rfl

def raw7914 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, 2, 1], ![2, 1, -3, 0]]

def raw7914step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, 2, -3], ![-1, 1, 0]]

def raw7914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, -2, 3], ![1, -1, 0]]

def raw7914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7914 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7914 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw7914 = injectiveMoment H raw7914step0 := by
      have heq : raw7914step0 = raw7914.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7914).symm
    injectiveMoment H raw7914step0 = injectiveMoment H raw7914step1 := by
      have heq : raw7914step1 = -raw7914step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7914step0).symm
    injectiveMoment H raw7914step1 = injectiveMoment H raw7914step2 := by
      have heq : raw7914step2 = (fun i j => raw7914step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7914step1 permutation24 permutation3
    _ = injectiveMoment H node261 := by rfl

def raw7915 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, 3, 0], ![2, 1, -4, 1]]

def raw7915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, 3, -4], ![-1, 0, 1]]

def raw7915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, -3, 4], ![1, 0, -1]]

def raw7915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7915 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7915 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw7915 = injectiveMoment H raw7915step0 := by
      have heq : raw7915step0 = raw7915.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7915).symm
    injectiveMoment H raw7915step0 = injectiveMoment H raw7915step1 := by
      have heq : raw7915step1 = -raw7915step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7915step0).symm
    injectiveMoment H raw7915step1 = injectiveMoment H raw7915step2 := by
      have heq : raw7915step2 = (fun i j => raw7915step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7915step1 permutation24 permutation3
    _ = injectiveMoment H node246 := by rfl

def raw7916 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, 1, 1, -1], ![2, -2, -2, 2]]

def raw7916step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![-1, -1, 2]]

def raw7916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7916 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7916 = injectiveMoment H node275 := by
  calc
    injectiveMoment H raw7916 = injectiveMoment H raw7916step0 := by
      have heq : raw7916step0 = raw7916.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7916).symm
    injectiveMoment H raw7916step0 = injectiveMoment H raw7916step1 := by
      have heq : raw7916step1 = (fun i j => raw7916step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7916step0 permutation13 permutation3
    _ = injectiveMoment H node275 := by rfl

def raw7917 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, 1, 2, -2], ![2, -2, -3, 3]]

def raw7917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 1, -2], ![1, 2, -3], ![-1, -2, 3]]

def raw7917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical7917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7917 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw7917 = injectiveMoment H raw7917step0 := by
      have heq : raw7917step0 = raw7917.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7917).symm
    injectiveMoment H raw7917step0 = injectiveMoment H raw7917step1 := by
      have heq : raw7917step1 = (fun i j => raw7917step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7917step0 permutation27 permutation3
    _ = injectiveMoment H node258 := by rfl

def raw7918 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -4, 2, 2], ![1, 3, -3, -1]]

def raw7918step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -4, 3], ![1, 2, -3], ![-1, 2, -1]]

def raw7918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 4, -3], ![-1, -2, 3], ![1, -2, 1]]

def raw7918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7918 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7918 = injectiveMoment H node247 := by
  calc
    injectiveMoment H raw7918 = injectiveMoment H raw7918step0 := by
      have heq : raw7918step0 = raw7918.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7918).symm
    injectiveMoment H raw7918step0 = injectiveMoment H raw7918step1 := by
      have heq : raw7918step1 = -raw7918step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7918step0).symm
    injectiveMoment H raw7918step1 = injectiveMoment H raw7918step2 := by
      have heq : raw7918step2 = (fun i j => raw7918step1 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7918step1 permutation17 permutation4
    _ = injectiveMoment H node247 := by rfl

def raw7919 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -3, 1, 2], ![1, 2, -2, -1]]

def raw7919step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![-1, 2, -1]]

def raw7919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -1, 2], ![1, -2, 1]]

def raw7919step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7919 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7919 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw7919 = injectiveMoment H raw7919step0 := by
      have heq : raw7919step0 = raw7919.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7919).symm
    injectiveMoment H raw7919step0 = injectiveMoment H raw7919step1 := by
      have heq : raw7919step1 = -raw7919step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7919step0).symm
    injectiveMoment H raw7919step1 = injectiveMoment H raw7919step2 := by
      have heq : raw7919step2 = (fun i j => raw7919step1 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7919step1 permutation17 permutation4
    _ = injectiveMoment H node261 := by rfl

def raw7920 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -3, 2, 1], ![1, 2, -3, 0]]

def raw7920step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -3, 2], ![1, 2, -3], ![-1, 1, 0]]

def raw7920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw7920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7920 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7920 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw7920 = injectiveMoment H raw7920step0 := by
      have heq : raw7920step0 = raw7920.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7920).symm
    injectiveMoment H raw7920step0 = injectiveMoment H raw7920step1 := by
      have heq : raw7920step1 = -raw7920step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7920step0).symm
    injectiveMoment H raw7920step1 = injectiveMoment H raw7920step2 := by
      have heq : raw7920step2 = (fun i j => raw7920step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7920step1 permutation24 permutation3
    _ = injectiveMoment H node263 := by rfl

def raw7921 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, -2, 4], ![1, 1, 1, -3]]

def raw7921step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![1, -2, 1], ![-1, 4, -3]]

def raw7921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7921 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7921 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw7921 = injectiveMoment H raw7921step0 := by
      have heq : raw7921step0 = raw7921.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7921).symm
    injectiveMoment H raw7921step0 = injectiveMoment H raw7921step1 := by
      have heq : raw7921step1 = (fun i j => raw7921step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7921step0 permutation27 permutation4
    _ = injectiveMoment H node244 := by rfl

def raw7922 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, 1, 1], ![1, 1, -2, 0]]

def raw7922step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![-1, 1, 0]]

def raw7922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7922 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw7922 = injectiveMoment H raw7922step0 := by
      have heq : raw7922step0 = raw7922.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7922).symm
    injectiveMoment H raw7922step0 = injectiveMoment H raw7922step1 := by
      have heq : raw7922step1 = (fun i j => raw7922step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7922step0 permutation16 permutation5
    _ = injectiveMoment H node230 := by rfl

def raw7923 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, 3, -1], ![1, 1, -4, 2]]

def raw7923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![1, 3, -4], ![-1, -1, 2]]

def raw7923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 2, -1], ![-1, -3, 4], ![1, 1, -2]]

def raw7923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7923 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7923 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw7923 = injectiveMoment H raw7923step0 := by
      have heq : raw7923step0 = raw7923.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7923).symm
    injectiveMoment H raw7923step0 = injectiveMoment H raw7923step1 := by
      have heq : raw7923step1 = -raw7923step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7923step0).symm
    injectiveMoment H raw7923step1 = injectiveMoment H raw7923step2 := by
      have heq : raw7923step2 = (fun i j => raw7923step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7923step1 permutation23 permutation3
    _ = injectiveMoment H node246 := by rfl

def raw7924 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7924step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, -1, 1], ![0, 1, 3, -4], ![0, -1, -1, 2], ![-1, 1, -1, 1]]

def raw7924step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical7924 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7924 = injectiveMoment H node1341 := by
  calc
    injectiveMoment H raw7924 = injectiveMoment H raw7924step0 := by
      have heq : raw7924step0 = -raw7924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7924).symm
    injectiveMoment H raw7924step0 = injectiveMoment H raw7924step1 := by
      have heq : raw7924step1 = (fun i j => raw7924step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7924step0 permutation32 permutation9
    _ = injectiveMoment H node1341 := by rfl

def raw7925 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7925step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical7925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7925 = injectiveMoment H node1262 := by
  calc
    injectiveMoment H raw7925 = injectiveMoment H raw7925step0 := by
      have heq : raw7925step0 = (fun i j => raw7925 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7925 permutation18 permutation21
    _ = injectiveMoment H node1262 := by rfl

def raw7926 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical7926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7926 = injectiveMoment H node1360 := by
  rfl

def raw7927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7927step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

theorem canonical7927 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7927 = injectiveMoment H node1349 := by
  calc
    injectiveMoment H raw7927 = injectiveMoment H raw7927step0 := by
      have heq : raw7927step0 = (fun i j => raw7927 (permutation11 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7927 permutation11 permutation12
    _ = injectiveMoment H node1349 := by rfl

def raw7928 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7928step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![1, 1, 0, -2], ![-1, 0, -1, 2]]

def raw7928step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical7928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7928 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw7928 = injectiveMoment H raw7928step0 := by
      have heq : raw7928step0 = raw7928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7928).symm
    injectiveMoment H raw7928step0 = injectiveMoment H raw7928step1 := by
      have heq : raw7928step1 = (fun i j => raw7928step0 (permutation28 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7928step0 permutation28 permutation23
    _ = injectiveMoment H node1260 := by rfl

def raw7929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, -1, 2]]

theorem canonical7929 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7929 = injectiveMoment H node1366 := by
  rfl

def raw7930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw7930step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical7930 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7930 = injectiveMoment H node1362 := by
  calc
    injectiveMoment H raw7930 = injectiveMoment H raw7930step0 := by
      have heq : raw7930step0 = (fun i j => raw7930 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7930 permutation9 permutation11
    _ = injectiveMoment H node1362 := by rfl

def raw7931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

theorem canonical7931 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7931 = injectiveMoment H node1367 := by
  rfl

def raw7932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7932step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 0, 1, -2], ![-1, 0, -2, 3]]

def raw7932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw7932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7932 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7932 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw7932 = injectiveMoment H raw7932step0 := by
      have heq : raw7932step0 = raw7932.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7932).symm
    injectiveMoment H raw7932step0 = injectiveMoment H raw7932step1 := by
      have hz : ∀ i, raw7932step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7932step1 = (fun i j => raw7932step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7932step0 permutation15 hz
    injectiveMoment H raw7932step1 = injectiveMoment H raw7932step2 := by
      have heq : raw7932step2 = (fun i j => raw7932step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7932step1 permutation27 permutation5
    _ = injectiveMoment H node175 := by rfl

def raw7933 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, -2, 2]]

def raw7933step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![1, 1, 0, -2], ![-1, -1, 0, 2]]

def raw7933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw7933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical7933 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7933 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw7933 = injectiveMoment H raw7933step0 := by
      have heq : raw7933step0 = raw7933.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7933).symm
    injectiveMoment H raw7933step0 = injectiveMoment H raw7933step1 := by
      have hz : ∀ i, raw7933step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw7933step1 = (fun i j => raw7933step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7933step0 permutation21 hz
    injectiveMoment H raw7933step1 = injectiveMoment H raw7933step2 := by
      have heq : raw7933step2 = (fun i j => raw7933step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7933step1 permutation27 permutation5
    _ = injectiveMoment H node283 := by rfl

def raw7934 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7934step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, 0, -2], ![-1, -1, -1, 3]]

def raw7934step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical7934 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7934 = injectiveMoment H node964 := by
  calc
    injectiveMoment H raw7934 = injectiveMoment H raw7934step0 := by
      have heq : raw7934step0 = raw7934.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7934).symm
    injectiveMoment H raw7934step0 = injectiveMoment H raw7934step1 := by
      have heq : raw7934step1 = (fun i j => raw7934step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7934step0 permutation27 permutation17
    _ = injectiveMoment H node964 := by rfl

def raw7935 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -3, 4]]

def raw7935step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, 1, -3], ![-1, -1, -2, 4]]

def raw7935step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, 1, -3]]

theorem canonical7935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7935 = injectiveMoment H node761 := by
  calc
    injectiveMoment H raw7935 = injectiveMoment H raw7935step0 := by
      have heq : raw7935step0 = raw7935.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7935).symm
    injectiveMoment H raw7935step0 = injectiveMoment H raw7935step1 := by
      have heq : raw7935step1 = (fun i j => raw7935step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7935step0 permutation27 permutation17
    _ = injectiveMoment H node761 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
