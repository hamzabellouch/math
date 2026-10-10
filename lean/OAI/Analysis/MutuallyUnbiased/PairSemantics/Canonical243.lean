import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7776 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def raw7776step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-3, 3, 0], ![3, -2, -1]]

def raw7776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7776 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw7776 = injectiveMoment H raw7776step0 := by
      have heq : raw7776step0 = raw7776.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7776).symm
    injectiveMoment H raw7776step0 = injectiveMoment H raw7776step1 := by
      have heq : raw7776step1 = (fun i j => raw7776step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7776step0 permutation30 permutation8
    _ = injectiveMoment H node269 := by rfl

def raw7777 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical7777 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7777 = injectiveMoment H node2836 := by
  rfl

def raw7778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7778step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw7778step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical7778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7778 = injectiveMoment H node1197 := by
  calc
    injectiveMoment H raw7778 = injectiveMoment H raw7778step0 := by
      have heq : raw7778step0 = raw7778.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7778).symm
    injectiveMoment H raw7778step0 = injectiveMoment H raw7778step1 := by
      have heq : raw7778step1 = (fun i j => raw7778step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7778step0 permutation29 permutation20
    _ = injectiveMoment H node1197 := by rfl

def raw7779 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7779step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 1, 0, 2], ![3, -1, -1, -1]]

def raw7779step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical7779 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7779 = injectiveMoment H node968 := by
  calc
    injectiveMoment H raw7779 = injectiveMoment H raw7779step0 := by
      have heq : raw7779step0 = raw7779.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7779).symm
    injectiveMoment H raw7779step0 = injectiveMoment H raw7779step1 := by
      have heq : raw7779step1 = (fun i j => raw7779step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7779step0 permutation27 permutation18
    _ = injectiveMoment H node968 := by rfl

def raw7780 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7780step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 1, 1, 1], ![3, -1, -2, 0]]

def raw7780step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

theorem canonical7780 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7780 = injectiveMoment H node800 := by
  calc
    injectiveMoment H raw7780 = injectiveMoment H raw7780step0 := by
      have heq : raw7780step0 = raw7780.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7780).symm
    injectiveMoment H raw7780step0 = injectiveMoment H raw7780step1 := by
      have heq : raw7780step1 = (fun i j => raw7780step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7780step0 permutation27 permutation18
    _ = injectiveMoment H node800 := by rfl

def raw7781 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![1, -1, 2, -2]]

def raw7781step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 1, 2], ![3, -1, -2]]

def raw7781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical7781 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7781 = injectiveMoment H node267 := by
  calc
    injectiveMoment H raw7781 = injectiveMoment H raw7781step0 := by
      have heq : raw7781step0 = raw7781.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7781).symm
    injectiveMoment H raw7781step0 = injectiveMoment H raw7781step1 := by
      have heq : raw7781step1 = (fun i j => raw7781step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7781step0 permutation29 permutation6
    _ = injectiveMoment H node267 := by rfl

def raw7782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 2, 0, 1], ![3, -2, -1, 0]]

def raw7782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical7782 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7782 = injectiveMoment H node803 := by
  calc
    injectiveMoment H raw7782 = injectiveMoment H raw7782step0 := by
      have heq : raw7782step0 = raw7782.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7782).symm
    injectiveMoment H raw7782step0 = injectiveMoment H raw7782step1 := by
      have heq : raw7782step1 = (fun i j => raw7782step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7782step0 permutation28 permutation24
    _ = injectiveMoment H node803 := by rfl

def raw7783 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7783step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 2, 1], ![3, -2, -1]]

def raw7783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical7783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7783 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw7783 = injectiveMoment H raw7783step0 := by
      have heq : raw7783step0 = raw7783.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7783).symm
    injectiveMoment H raw7783step0 = injectiveMoment H raw7783step1 := by
      have heq : raw7783step1 = (fun i j => raw7783step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7783step0 permutation29 permutation6
    _ = injectiveMoment H node168 := by rfl

def raw7784 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7784step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 3, 0], ![3, -3, 0]]

def raw7784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7784 = injectiveMoment H node289 := by
  calc
    injectiveMoment H raw7784 = injectiveMoment H raw7784step0 := by
      have heq : raw7784step0 = raw7784.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7784).symm
    injectiveMoment H raw7784step0 = injectiveMoment H raw7784step1 := by
      have heq : raw7784step1 = (fun i j => raw7784step0 (permutation20 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7784step0 permutation20 permutation8
    _ = injectiveMoment H node289 := by rfl

def raw7785 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 4, -4], ![1, -1, -1, 1]]

def raw7785step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 4, -1], ![3, -4, 1]]

def raw7785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7785 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7785 = injectiveMoment H node242 := by
  calc
    injectiveMoment H raw7785 = injectiveMoment H raw7785step0 := by
      have heq : raw7785step0 = raw7785.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7785).symm
    injectiveMoment H raw7785step0 = injectiveMoment H raw7785step1 := by
      have heq : raw7785step1 = (fun i j => raw7785step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7785step0 permutation23 permutation7
    _ = injectiveMoment H node242 := by rfl

def raw7786 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7786step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-3, 1, 2], ![3, -2, -1]]

def raw7786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical7786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7786 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw7786 = injectiveMoment H raw7786step0 := by
      have heq : raw7786step0 = raw7786.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7786).symm
    injectiveMoment H raw7786step0 = injectiveMoment H raw7786step1 := by
      have heq : raw7786step1 = (fun i j => raw7786step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7786step0 permutation27 permutation6
    _ = injectiveMoment H node180 := by rfl

def raw7787 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7787step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-3, 2, 1], ![3, -3, 0]]

def raw7787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7787 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7787 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw7787 = injectiveMoment H raw7787step0 := by
      have heq : raw7787step0 = raw7787.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7787).symm
    injectiveMoment H raw7787step0 = injectiveMoment H raw7787step1 := by
      have heq : raw7787step1 = (fun i j => raw7787step0 (permutation19 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7787step0 permutation19 permutation8
    _ = injectiveMoment H node222 := by rfl

def raw7788 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7788step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-3, 3, 0], ![3, -4, 1]]

def raw7788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7788 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7788 = injectiveMoment H node221 := by
  calc
    injectiveMoment H raw7788 = injectiveMoment H raw7788step0 := by
      have heq : raw7788step0 = raw7788.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7788).symm
    injectiveMoment H raw7788step0 = injectiveMoment H raw7788step1 := by
      have heq : raw7788step1 = (fun i j => raw7788step0 (permutation17 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7788step0 permutation17 permutation7
    _ = injectiveMoment H node221 := by rfl

def raw7789 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical7789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7789 = injectiveMoment H node2837 := by
  rfl

def raw7790 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical7790 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7790 = injectiveMoment H node2838 := by
  rfl

def raw7791 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical7791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7791 = injectiveMoment H node2839 := by
  rfl

def raw7792 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw7792step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical7792 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7792 = injectiveMoment H node2839 := by
  calc
    injectiveMoment H raw7792 = injectiveMoment H raw7792step0 := by
      have heq : raw7792step0 = (fun i j => raw7792 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7792 permutation34 permutation9
    _ = injectiveMoment H node2839 := by rfl

def raw7793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![2, -2, 1, -1]]

def raw7793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 1, 0, -2], ![-2, -1, 2, 1], ![2, 1, -2, -1]]

def raw7793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, -1, 1, -2]]

theorem canonical7793 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7793 = injectiveMoment H node678 := by
  calc
    injectiveMoment H raw7793 = injectiveMoment H raw7793step0 := by
      have heq : raw7793step0 = raw7793.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7793).symm
    injectiveMoment H raw7793step0 = injectiveMoment H raw7793step1 := by
      have heq : raw7793step1 = (fun i j => raw7793step0 (permutation27 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7793step0 permutation27 permutation24
    _ = injectiveMoment H node678 := by rfl

def raw7794 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical7794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7794 = injectiveMoment H node2840 := by
  rfl

def raw7795 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![2, -2, 0, 0]]

def raw7795step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 1, 0, -2], ![-2, -1, 3, 0], ![2, 1, -3, 0]]

def raw7795step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]

theorem canonical7795 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7795 = injectiveMoment H node689 := by
  calc
    injectiveMoment H raw7795 = injectiveMoment H raw7795step0 := by
      have heq : raw7795step0 = raw7795.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7795).symm
    injectiveMoment H raw7795step0 = injectiveMoment H raw7795step1 := by
      have heq : raw7795step1 = (fun i j => raw7795step0 (permutation18 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7795step0 permutation18 permutation30
    _ = injectiveMoment H node689 := by rfl

def raw7796 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw7796step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw7796step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical7796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7796 = injectiveMoment H node1359 := by
  calc
    injectiveMoment H raw7796 = injectiveMoment H raw7796step0 := by
      have heq : raw7796step0 = raw7796.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7796).symm
    injectiveMoment H raw7796step0 = injectiveMoment H raw7796step1 := by
      have heq : raw7796step1 = (fun i j => raw7796step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7796step0 permutation18 permutation23
    _ = injectiveMoment H node1359 := by rfl

def raw7797 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical7797 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7797 = injectiveMoment H node1330 := by
  rfl

def raw7798 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw7798step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical7798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7798 = injectiveMoment H node1330 := by
  calc
    injectiveMoment H raw7798 = injectiveMoment H raw7798step0 := by
      have heq : raw7798step0 = (fun i j => raw7798 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7798 permutation10 permutation9
    _ = injectiveMoment H node1330 := by rfl

def raw7799 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, -1, 0, 0]]

def raw7799step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, -1, 3, 0], ![2, 1, -3, 0]]

def raw7799step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical7799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7799 = injectiveMoment H node1359 := by
  calc
    injectiveMoment H raw7799 = injectiveMoment H raw7799step0 := by
      have heq : raw7799step0 = raw7799.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7799).symm
    injectiveMoment H raw7799step0 = injectiveMoment H raw7799step1 := by
      have heq : raw7799step1 = (fun i j => raw7799step0 (permutation18 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7799step0 permutation18 permutation29
    _ = injectiveMoment H node1359 := by rfl

def raw7800 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7800step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical7800 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7800 = injectiveMoment H node1748 := by
  calc
    injectiveMoment H raw7800 = injectiveMoment H raw7800step0 := by
      have heq : raw7800step0 = (fun i j => raw7800 (permutation35 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7800 permutation35 permutation21
    _ = injectiveMoment H node1748 := by rfl

def raw7801 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7801step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical7801 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7801 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw7801 = injectiveMoment H raw7801step0 := by
      have heq : raw7801step0 = (fun i j => raw7801 (permutation36 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7801 permutation36 permutation21
    _ = injectiveMoment H node1746 := by rfl

def raw7802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7802step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 0, 0, 2], ![2, 0, 0, -2]]

def raw7802step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem canonical7802 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7802 = injectiveMoment H node1344 := by
  calc
    injectiveMoment H raw7802 = injectiveMoment H raw7802step0 := by
      have heq : raw7802step0 = raw7802.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7802).symm
    injectiveMoment H raw7802step0 = injectiveMoment H raw7802step1 := by
      have heq : raw7802step1 = (fun i j => raw7802step0 (permutation12 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7802step0 permutation12 permutation17
    _ = injectiveMoment H node1344 := by rfl

def raw7803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7803step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 0, 1, 1], ![2, 0, -1, -1]]

def raw7803step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical7803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7803 = injectiveMoment H node1360 := by
  calc
    injectiveMoment H raw7803 = injectiveMoment H raw7803step0 := by
      have heq : raw7803step0 = raw7803.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7803).symm
    injectiveMoment H raw7803step0 = injectiveMoment H raw7803step1 := by
      have heq : raw7803step1 = (fun i j => raw7803step0 (permutation14 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7803step0 permutation14 permutation18
    _ = injectiveMoment H node1360 := by rfl

def raw7804 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7804step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical7804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7804 = injectiveMoment H node1823 := by
  calc
    injectiveMoment H raw7804 = injectiveMoment H raw7804step0 := by
      have heq : raw7804step0 = (fun i j => raw7804 (permutation49 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7804 permutation49 permutation21
    _ = injectiveMoment H node1823 := by rfl

def raw7805 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7805step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw7805step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical7805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7805 = injectiveMoment H node1096 := by
  calc
    injectiveMoment H raw7805 = injectiveMoment H raw7805step0 := by
      have heq : raw7805step0 = raw7805.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7805).symm
    injectiveMoment H raw7805step0 = injectiveMoment H raw7805step1 := by
      have heq : raw7805step1 = (fun i j => raw7805step0 (permutation20 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7805step0 permutation20 permutation26
    _ = injectiveMoment H node1096 := by rfl

def raw7806 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7806step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 2, 0, 0], ![2, -2, 0, 0]]

def raw7806step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical7806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7806 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw7806 = injectiveMoment H raw7806step0 := by
      have heq : raw7806step0 = raw7806.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7806).symm
    injectiveMoment H raw7806step0 = injectiveMoment H raw7806step1 := by
      have heq : raw7806step1 = (fun i j => raw7806step0 (permutation18 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7806step0 permutation18 permutation25
    _ = injectiveMoment H node1107 := by rfl

def raw7807 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7807step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 3, -1, 0], ![2, -3, 1, 0]]

def raw7807step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical7807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7807 = injectiveMoment H node1092 := by
  calc
    injectiveMoment H raw7807 = injectiveMoment H raw7807step0 := by
      have heq : raw7807step0 = raw7807.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7807).symm
    injectiveMoment H raw7807step0 = injectiveMoment H raw7807step1 := by
      have heq : raw7807step1 = (fun i j => raw7807step0 (permutation18 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7807step0 permutation18 permutation31
    _ = injectiveMoment H node1092 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
