import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw7136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -3, 2], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw7136step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical7136 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7136 = injectiveMoment H node1123 := by
  calc
    injectiveMoment H raw7136 = injectiveMoment H raw7136step0 := by
      have heq : raw7136step0 = -raw7136 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7136).symm
    injectiveMoment H raw7136step0 = injectiveMoment H raw7136step1 := by
      have heq : raw7136step1 = (fun i j => raw7136step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7136step0 permutation29 permutation15
    _ = injectiveMoment H node1123 := by rfl

def raw7137 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw7137step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -3, 2], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw7137step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical7137 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7137 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw7137 = injectiveMoment H raw7137step0 := by
      have heq : raw7137step0 = -raw7137 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7137).symm
    injectiveMoment H raw7137step0 = injectiveMoment H raw7137step1 := by
      have heq : raw7137step1 = (fun i j => raw7137step0 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7137step0 permutation27 permutation16
    _ = injectiveMoment H node1079 := by rfl

def raw7138 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -2, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7138step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, -2, 0, 3], ![2, 2, 0, -4]]

def raw7138step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical7138 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7138 = injectiveMoment H node1298 := by
  calc
    injectiveMoment H raw7138 = injectiveMoment H raw7138step0 := by
      have heq : raw7138step0 = raw7138.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7138).symm
    injectiveMoment H raw7138step0 = injectiveMoment H raw7138step1 := by
      have heq : raw7138step1 = (fun i j => raw7138step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7138step0 permutation18 permutation21
    _ = injectiveMoment H node1298 := by rfl

def raw7139 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw7139step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, -2, 3, 0], ![2, 2, -3, -1]]

def raw7139step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![1, 2, -3, 0], ![-2, -2, 3, 1]]

def raw7139step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

theorem canonical7139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7139 = injectiveMoment H node1367 := by
  calc
    injectiveMoment H raw7139 = injectiveMoment H raw7139step0 := by
      have heq : raw7139step0 = raw7139.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7139).symm
    injectiveMoment H raw7139step0 = injectiveMoment H raw7139step1 := by
      have heq : raw7139step1 = -raw7139step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7139step0).symm
    injectiveMoment H raw7139step1 = injectiveMoment H raw7139step2 := by
      have heq : raw7139step2 = (fun i j => raw7139step1 (permutation9 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7139step1 permutation9 permutation27
    _ = injectiveMoment H node1367 := by rfl

def raw7140 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw7140step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical7140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7140 = injectiveMoment H node1341 := by
  calc
    injectiveMoment H raw7140 = injectiveMoment H raw7140step0 := by
      have heq : raw7140step0 = (fun i j => raw7140 (permutation22 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7140 permutation22 permutation15
    _ = injectiveMoment H node1341 := by rfl

def raw7141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw7141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical7141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7141 = injectiveMoment H node1360 := by
  calc
    injectiveMoment H raw7141 = injectiveMoment H raw7141step0 := by
      have heq : raw7141step0 = (fun i j => raw7141 (permutation22 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7141 permutation22 permutation15
    _ = injectiveMoment H node1360 := by rfl

def raw7142 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw7142step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, -1, 3, -1], ![2, 1, -3, 0]]

def raw7142step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical7142 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7142 = injectiveMoment H node972 := by
  calc
    injectiveMoment H raw7142 = injectiveMoment H raw7142step0 := by
      have heq : raw7142step0 = raw7142.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7142).symm
    injectiveMoment H raw7142step0 = injectiveMoment H raw7142step1 := by
      have heq : raw7142step1 = (fun i j => raw7142step0 (permutation24 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7142step0 permutation24 permutation27
    _ = injectiveMoment H node972 := by rfl

def raw7143 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw7143step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -1, 1, -1], ![-1, 0, 0, 1], ![-1, 1, -2, 2]]

def raw7143step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical7143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7143 = injectiveMoment H node1362 := by
  calc
    injectiveMoment H raw7143 = injectiveMoment H raw7143step0 := by
      have heq : raw7143step0 = -raw7143 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7143).symm
    injectiveMoment H raw7143step0 = injectiveMoment H raw7143step1 := by
      have heq : raw7143step1 = (fun i j => raw7143step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7143step0 permutation17 permutation15
    _ = injectiveMoment H node1362 := by rfl

def raw7144 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw7144step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical7144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7144 = injectiveMoment H node1333 := by
  calc
    injectiveMoment H raw7144 = injectiveMoment H raw7144step0 := by
      have heq : raw7144step0 = (fun i j => raw7144 (permutation22 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7144 permutation22 permutation16
    _ = injectiveMoment H node1333 := by rfl

def raw7145 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7145step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical7145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7145 = injectiveMoment H node1785 := by
  calc
    injectiveMoment H raw7145 = injectiveMoment H raw7145step0 := by
      have heq : raw7145step0 = (fun i j => raw7145 (permutation65 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7145 permutation65 permutation27
    _ = injectiveMoment H node1785 := by rfl

def raw7146 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical7146 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7146 = injectiveMoment H node2713 := by
  rfl

def raw7147 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw7147step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw7147step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

theorem canonical7147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7147 = injectiveMoment H node475 := by
  calc
    injectiveMoment H raw7147 = injectiveMoment H raw7147step0 := by
      have heq : raw7147step0 = raw7147.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7147).symm
    injectiveMoment H raw7147step0 = injectiveMoment H raw7147step1 := by
      have heq : raw7147step1 = (fun i j => raw7147step0 (permutation21 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7147step0 permutation21 permutation22
    _ = injectiveMoment H node475 := by rfl

def raw7148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical7148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7148 = injectiveMoment H node2714 := by
  rfl

def raw7149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw7149step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical7149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7149 = injectiveMoment H node2714 := by
  calc
    injectiveMoment H raw7149 = injectiveMoment H raw7149step0 := by
      have heq : raw7149step0 = (fun i j => raw7149 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7149 permutation34 permutation9
    _ = injectiveMoment H node2714 := by rfl

def raw7150 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw7150step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, 3, -1, -1], ![2, -3, 1, 0]]

def raw7150step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical7150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7150 = injectiveMoment H node933 := by
  calc
    injectiveMoment H raw7150 = injectiveMoment H raw7150step0 := by
      have heq : raw7150step0 = raw7150.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7150).symm
    injectiveMoment H raw7150step0 = injectiveMoment H raw7150step1 := by
      have heq : raw7150step1 = (fun i j => raw7150step0 (permutation24 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7150step0 permutation24 permutation31
    _ = injectiveMoment H node933 := by rfl

def raw7151 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw7151step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw7151step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 0, 1], ![1, -3, 2, 0], ![-2, 3, -1, 0]]

def raw7151step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical7151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7151 = injectiveMoment H node1094 := by
  calc
    injectiveMoment H raw7151 = injectiveMoment H raw7151step0 := by
      have heq : raw7151step0 = raw7151.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7151).symm
    injectiveMoment H raw7151step0 = injectiveMoment H raw7151step1 := by
      have heq : raw7151step1 = -raw7151step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7151step0).symm
    injectiveMoment H raw7151step1 = injectiveMoment H raw7151step2 := by
      have heq : raw7151step2 = (fun i j => raw7151step1 (permutation14 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7151step1 permutation14 permutation31
    _ = injectiveMoment H node1094 := by rfl

def raw7152 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 2, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw7152step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -2, 2, -1], ![-1, 1, -1, 1], ![-1, 1, -2, 2]]

def raw7152step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical7152 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7152 = injectiveMoment H node685 := by
  calc
    injectiveMoment H raw7152 = injectiveMoment H raw7152step0 := by
      have heq : raw7152step0 = -raw7152 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7152).symm
    injectiveMoment H raw7152step0 = injectiveMoment H raw7152step1 := by
      have heq : raw7152step1 = (fun i j => raw7152step0 (permutation15 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7152step0 permutation15 permutation16
    _ = injectiveMoment H node685 := by rfl

def raw7153 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 2, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7153step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -1, -1], ![-1, 2, -1, 0], ![2, -3, 1, 0]]

def raw7153step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical7153 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7153 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw7153 = injectiveMoment H raw7153step0 := by
      have heq : raw7153step0 = raw7153.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7153).symm
    injectiveMoment H raw7153step0 = injectiveMoment H raw7153step1 := by
      have heq : raw7153step1 = (fun i j => raw7153step0 (permutation18 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7153step0 permutation18 permutation31
    _ = injectiveMoment H node995 := by rfl

def raw7154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw7154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, 0, -2], ![0, -1, -3, 4], ![-1, -1, 2, 0]]

def raw7154step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical7154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7154 = injectiveMoment H node1155 := by
  calc
    injectiveMoment H raw7154 = injectiveMoment H raw7154step0 := by
      have heq : raw7154step0 = -raw7154 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7154).symm
    injectiveMoment H raw7154step0 = injectiveMoment H raw7154step1 := by
      have heq : raw7154step1 = (fun i j => raw7154step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7154step0 permutation32 permutation9
    _ = injectiveMoment H node1155 := by rfl

def raw7155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7155step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical7155 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7155 = injectiveMoment H node1037 := by
  calc
    injectiveMoment H raw7155 = injectiveMoment H raw7155step0 := by
      have heq : raw7155step0 = (fun i j => raw7155 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7155 permutation9 permutation11
    _ = injectiveMoment H node1037 := by rfl

def raw7156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw7156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -1, -1], ![0, -1, 2, -1], ![-1, -1, -2, 4]]

def raw7156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical7156 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7156 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw7156 = injectiveMoment H raw7156step0 := by
      have heq : raw7156step0 = -raw7156 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7156).symm
    injectiveMoment H raw7156step0 = injectiveMoment H raw7156step1 := by
      have heq : raw7156step1 = (fun i j => raw7156step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7156step0 permutation32 permutation9
    _ = injectiveMoment H node896 := by rfl

def raw7157 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical7157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7157 = injectiveMoment H node2717 := by
  rfl

def raw7158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw7158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -1, -1], ![0, -1, -2, 3], ![-1, -1, 2, 0]]

def raw7158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical7158 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7158 = injectiveMoment H node1016 := by
  calc
    injectiveMoment H raw7158 = injectiveMoment H raw7158step0 := by
      have heq : raw7158step0 = -raw7158 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7158).symm
    injectiveMoment H raw7158step0 = injectiveMoment H raw7158step1 := by
      have heq : raw7158step1 = (fun i j => raw7158step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7158step0 permutation32 permutation10
    _ = injectiveMoment H node1016 := by rfl

def raw7159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical7159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7159 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw7159 = injectiveMoment H raw7159step0 := by
      have heq : raw7159step0 = (fun i j => raw7159 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7159 permutation9 permutation11
    _ = injectiveMoment H node1079 := by rfl

def raw7160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical7160 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7160 = injectiveMoment H node1234 := by
  rfl

def raw7161 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7161step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical7161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7161 = injectiveMoment H node1008 := by
  calc
    injectiveMoment H raw7161 = injectiveMoment H raw7161step0 := by
      have heq : raw7161step0 = (fun i j => raw7161 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7161 permutation11 permutation11
    _ = injectiveMoment H node1008 := by rfl

def raw7162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw7162step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical7162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7162 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw7162 = injectiveMoment H raw7162step0 := by
      have heq : raw7162step0 = (fun i j => raw7162 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7162 permutation11 permutation11
    _ = injectiveMoment H node1057 := by rfl

def raw7163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical7163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7163 = injectiveMoment H node1235 := by
  rfl

def raw7164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw7164step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -3, 1], ![0, -1, 2, -1], ![-1, -1, 0, 2]]

def raw7164step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical7164 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7164 = injectiveMoment H node1007 := by
  calc
    injectiveMoment H raw7164 = injectiveMoment H raw7164step0 := by
      have heq : raw7164step0 = -raw7164 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7164).symm
    injectiveMoment H raw7164step0 = injectiveMoment H raw7164step1 := by
      have heq : raw7164step1 = (fun i j => raw7164step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7164step0 permutation32 permutation9
    _ = injectiveMoment H node1007 := by rfl

def raw7165 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7165step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -3, 1], ![0, -2, 2, 0], ![-1, 0, 0, 1]]

def raw7165step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical7165 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7165 = injectiveMoment H node1296 := by
  calc
    injectiveMoment H raw7165 = injectiveMoment H raw7165step0 := by
      have heq : raw7165step0 = -raw7165 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7165).symm
    injectiveMoment H raw7165step0 = injectiveMoment H raw7165step1 := by
      have heq : raw7165step1 = (fun i j => raw7165step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7165step0 permutation32 permutation10
    _ = injectiveMoment H node1296 := by rfl

def raw7166 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical7166 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7166 = injectiveMoment H node2721 := by
  rfl

def raw7167 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw7167step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 0, -3, 4]]

def raw7167step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical7167 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7167 = injectiveMoment H node1168 := by
  calc
    injectiveMoment H raw7167 = injectiveMoment H raw7167step0 := by
      have heq : raw7167step0 = -raw7167 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7167).symm
    injectiveMoment H raw7167step0 = injectiveMoment H raw7167step1 := by
      have heq : raw7167step1 = (fun i j => raw7167step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7167step0 permutation32 permutation9
    _ = injectiveMoment H node1168 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
