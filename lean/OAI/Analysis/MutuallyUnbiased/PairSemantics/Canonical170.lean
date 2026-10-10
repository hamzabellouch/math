import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5440 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw5440step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, 1, -2, 1], ![0, -1, 2, -1]]

def raw5440step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical5440 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5440 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw5440 = injectiveMoment H raw5440step0 := by
      have heq : raw5440step0 = raw5440.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5440).symm
    injectiveMoment H raw5440step0 = injectiveMoment H raw5440step1 := by
      have heq : raw5440step1 = (fun i j => raw5440step0 (permutation29 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5440step0 permutation29 permutation19
    _ = injectiveMoment H node1005 := by rfl

def raw5441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw5441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, 2, -2, 0], ![0, -2, 2, 0]]

def raw5441step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5441 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5441 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw5441 = injectiveMoment H raw5441step0 := by
      have heq : raw5441step0 = raw5441.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5441).symm
    injectiveMoment H raw5441step0 = injectiveMoment H raw5441step1 := by
      have heq : raw5441step1 = (fun i j => raw5441step0 (permutation20 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5441step0 permutation20 permutation29
    _ = injectiveMoment H node1304 := by rfl

def raw5442 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw5442step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical5442 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5442 = injectiveMoment H node608 := by
  calc
    injectiveMoment H raw5442 = injectiveMoment H raw5442step0 := by
      have heq : raw5442step0 = (fun i j => raw5442 (permutation9 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5442 permutation9 permutation14
    _ = injectiveMoment H node608 := by rfl

def raw5443 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![1, -2, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw5443step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -2, 0, 0], ![0, -3, 2, 1], ![0, 4, -2, -2]]

def raw5443step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem canonical5443 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5443 = injectiveMoment H node394 := by
  calc
    injectiveMoment H raw5443 = injectiveMoment H raw5443step0 := by
      have heq : raw5443step0 = raw5443.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5443).symm
    injectiveMoment H raw5443step0 = injectiveMoment H raw5443step1 := by
      have heq : raw5443step1 = (fun i j => raw5443step0 (permutation29 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5443step0 permutation29 permutation25
    _ = injectiveMoment H node394 := by rfl

def raw5444 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![1, -1, -3, 3], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw5444step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, -1, 0], ![0, -3, 2, 1], ![0, 3, -1, -2]]

def raw5444step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

theorem canonical5444 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5444 = injectiveMoment H node475 := by
  calc
    injectiveMoment H raw5444 = injectiveMoment H raw5444step0 := by
      have heq : raw5444step0 = raw5444.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5444).symm
    injectiveMoment H raw5444step0 = injectiveMoment H raw5444step1 := by
      have heq : raw5444step1 = (fun i j => raw5444step0 (permutation29 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5444step0 permutation29 permutation31
    _ = injectiveMoment H node475 := by rfl

def raw5445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![1, -1, -3, 3], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw5445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, 0, -1], ![0, -3, 2, 1], ![0, 3, -2, -1]]

def raw5445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem canonical5445 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5445 = injectiveMoment H node471 := by
  calc
    injectiveMoment H raw5445 = injectiveMoment H raw5445step0 := by
      have heq : raw5445step0 = raw5445.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5445).symm
    injectiveMoment H raw5445step0 = injectiveMoment H raw5445step1 := by
      have heq : raw5445step1 = (fun i j => raw5445step0 (permutation29 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5445step0 permutation29 permutation25
    _ = injectiveMoment H node471 := by rfl

def raw5446 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5446step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -2, -1, 1], ![0, 1, 3, -4], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw5446step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical5446 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5446 = injectiveMoment H node2348 := by
  calc
    injectiveMoment H raw5446 = injectiveMoment H raw5446step0 := by
      have heq : raw5446step0 = -raw5446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5446).symm
    injectiveMoment H raw5446step0 = injectiveMoment H raw5446step1 := by
      have heq : raw5446step1 = (fun i j => raw5446step0 (permutation54 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5446step0 permutation54 permutation15
    _ = injectiveMoment H node2348 := by rfl

def raw5447 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5447step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -2, -1, 1], ![0, 1, 3, -4], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw5447step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem canonical5447 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5447 = injectiveMoment H node2349 := by
  calc
    injectiveMoment H raw5447 = injectiveMoment H raw5447step0 := by
      have heq : raw5447step0 = -raw5447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5447).symm
    injectiveMoment H raw5447step0 = injectiveMoment H raw5447step1 := by
      have heq : raw5447step1 = (fun i j => raw5447step0 (permutation54 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5447step0 permutation54 permutation15
    _ = injectiveMoment H node2349 := by rfl

def raw5448 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5448step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![1, -3, 0, 2], ![-1, 4, 0, -3]]

def raw5448step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![-1, 3, 0, -2], ![1, -4, 0, 3]]

def raw5448step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, -1, 3], ![0, 3, 1, -4], ![1, 0, -2, 1]]

theorem canonical5448 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5448 = injectiveMoment H node1154 := by
  calc
    injectiveMoment H raw5448 = injectiveMoment H raw5448step0 := by
      have heq : raw5448step0 = raw5448.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5448).symm
    injectiveMoment H raw5448step0 = injectiveMoment H raw5448step1 := by
      have heq : raw5448step1 = -raw5448step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5448step0).symm
    injectiveMoment H raw5448step1 = injectiveMoment H raw5448step2 := by
      have heq : raw5448step2 = (fun i j => raw5448step1 (permutation12 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5448step1 permutation12 permutation25
    _ = injectiveMoment H node1154 := by rfl

def raw5449 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5449step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![1, -3, 1, 1], ![-1, 4, -1, -2]]

def raw5449step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

theorem canonical5449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5449 = injectiveMoment H node453 := by
  calc
    injectiveMoment H raw5449 = injectiveMoment H raw5449step0 := by
      have heq : raw5449step0 = raw5449.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5449).symm
    injectiveMoment H raw5449step0 = injectiveMoment H raw5449step1 := by
      have heq : raw5449step1 = (fun i j => raw5449step0 (permutation29 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5449step0 permutation29 permutation31
    _ = injectiveMoment H node453 := by rfl

def raw5450 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw5450step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![1, -3, 2, 0], ![-1, 4, -2, -1]]

def raw5450step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 1, -2, 0]]

theorem canonical5450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5450 = injectiveMoment H node758 := by
  calc
    injectiveMoment H raw5450 = injectiveMoment H raw5450step0 := by
      have heq : raw5450step0 = raw5450.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5450).symm
    injectiveMoment H raw5450step0 = injectiveMoment H raw5450step1 := by
      have heq : raw5450step1 = (fun i j => raw5450step0 (permutation30 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5450step0 permutation30 permutation31
    _ = injectiveMoment H node758 := by rfl

def raw5451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![1, -3, 0, 2], ![-1, 3, 0, -2]]

def raw5451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

theorem canonical5451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5451 = injectiveMoment H node989 := by
  calc
    injectiveMoment H raw5451 = injectiveMoment H raw5451step0 := by
      have heq : raw5451step0 = raw5451.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5451).symm
    injectiveMoment H raw5451step0 = injectiveMoment H raw5451step1 := by
      have heq : raw5451step1 = (fun i j => raw5451step0 (permutation20 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5451step0 permutation20 permutation26
    _ = injectiveMoment H node989 := by rfl

def raw5452 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5452step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![1, -2, -1, 2], ![-1, 2, 1, -2]]

def raw5452step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, -1, -2]]

theorem canonical5452 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5452 = injectiveMoment H node503 := by
  calc
    injectiveMoment H raw5452 = injectiveMoment H raw5452step0 := by
      have heq : raw5452step0 = raw5452.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5452).symm
    injectiveMoment H raw5452step0 = injectiveMoment H raw5452step1 := by
      have heq : raw5452step1 = (fun i j => raw5452step0 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5452step0 permutation23 permutation17
    _ = injectiveMoment H node503 := by rfl

def raw5453 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, 2, 2, -2], ![2, -2, -2, 2]]

def raw5453step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![2, -2], ![-2, 2]]

def raw5453step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

theorem canonical5453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5453 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw5453 = injectiveMoment H raw5453step0 := by
      have heq : raw5453step0 = raw5453.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5453).symm
    injectiveMoment H raw5453step0 = injectiveMoment H raw5453step1 := by
      have heq : raw5453step1 = (fun i j => raw5453step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5453step0 permutation13 permutation1
    _ = injectiveMoment H node45 := by rfl

def raw5454 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 3, -3], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5454step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![3, -3, 0, 0], ![-3, 4, 0, -1]]

def raw5454step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![-3, 3, 0, 0], ![3, -4, 0, 1]]

def raw5454step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -4, 3], ![1, 0, 1, -2]]

theorem canonical5454 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5454 = injectiveMoment H node1061 := by
  calc
    injectiveMoment H raw5454 = injectiveMoment H raw5454step0 := by
      have heq : raw5454step0 = raw5454.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5454).symm
    injectiveMoment H raw5454step0 = injectiveMoment H raw5454step1 := by
      have heq : raw5454step1 = -raw5454step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5454step0).symm
    injectiveMoment H raw5454step1 = injectiveMoment H raw5454step2 := by
      have heq : raw5454step2 = (fun i j => raw5454step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5454step1 permutation12 permutation26
    _ = injectiveMoment H node1061 := by rfl

def raw5455 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 3, -3], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5455step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![3, -2, -1, 0], ![-3, 3, 1, -1]]

def raw5455step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![-3, 2, 1, 0], ![3, -3, -1, 1]]

def raw5455step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -1, -3, 3]]

theorem canonical5455 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5455 = injectiveMoment H node1085 := by
  calc
    injectiveMoment H raw5455 = injectiveMoment H raw5455step0 := by
      have heq : raw5455step0 = raw5455.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5455).symm
    injectiveMoment H raw5455step0 = injectiveMoment H raw5455step1 := by
      have heq : raw5455step1 = -raw5455step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5455step0).symm
    injectiveMoment H raw5455step1 = injectiveMoment H raw5455step2 := by
      have heq : raw5455step2 = (fun i j => raw5455step1 (permutation9 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5455step1 permutation9 permutation32
    _ = injectiveMoment H node1085 := by rfl

def raw5456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 3, -3], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5456step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -2, -3, 3], ![0, 1, 1, -2], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw5456step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical5456 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5456 = injectiveMoment H node2328 := by
  calc
    injectiveMoment H raw5456 = injectiveMoment H raw5456step0 := by
      have heq : raw5456step0 = -raw5456 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5456).symm
    injectiveMoment H raw5456step0 = injectiveMoment H raw5456step1 := by
      have heq : raw5456step1 = (fun i j => raw5456step0 (permutation54 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5456step0 permutation54 permutation15
    _ = injectiveMoment H node2328 := by rfl

def raw5457 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 3, -3], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw5457step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![3, -1, -2, 0], ![-3, 2, 2, -1]]

def raw5457step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![-3, 1, 2, 0], ![3, -2, -2, 1]]

def raw5457step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -2, -2, 3]]

theorem canonical5457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5457 = injectiveMoment H node1279 := by
  calc
    injectiveMoment H raw5457 = injectiveMoment H raw5457step0 := by
      have heq : raw5457step0 = raw5457.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5457).symm
    injectiveMoment H raw5457step0 = injectiveMoment H raw5457step1 := by
      have heq : raw5457step1 = -raw5457step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5457step0).symm
    injectiveMoment H raw5457step1 = injectiveMoment H raw5457step2 := by
      have heq : raw5457step2 = (fun i j => raw5457step1 (permutation9 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5457step1 permutation9 permutation30
    _ = injectiveMoment H node1279 := by rfl

def raw5458 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 3, -1], ![2, -3, 1]]

def raw5458step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![3, -3], ![-1, 1]]

def raw5458step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5459 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 4, -2], ![2, -4, 2]]

def raw5459step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![4, -4], ![-2, 2]]

def raw5459step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

theorem canonical5459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5459 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw5459 = injectiveMoment H raw5459step0 := by
      have heq : raw5459step0 = raw5459.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5459).symm
    injectiveMoment H raw5459step0 = injectiveMoment H raw5459step1 := by
      have heq : raw5459step1 = (fun i j => raw5459step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5459step0 permutation5 permutation2
    _ = injectiveMoment H node9 := by rfl

def raw5460 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 5, -3], ![2, -5, 3]]

def raw5460step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![5, -5], ![-3, 3]]

def raw5460step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

theorem canonical5460 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5460 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw5460 = injectiveMoment H raw5460step0 := by
      have heq : raw5460step0 = raw5460.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5460).symm
    injectiveMoment H raw5460step0 = injectiveMoment H raw5460step1 := by
      have heq : raw5460step1 = (fun i j => raw5460step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5460step0 permutation5 permutation2
    _ = injectiveMoment H node7 := by rfl

def raw5461 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5461 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5461 = injectiveMoment H node721 := by
  rfl

def raw5462 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical5462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5462 = injectiveMoment H node233 := by
  rfl

def raw5463 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5463 = injectiveMoment H node234 := by
  rfl

def raw5464 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![2, 2, -4]]

def raw5464step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![-2, -2, 4]]

def raw5464step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 4, -5]]

theorem canonical5464 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5464 = injectiveMoment H node34 := by
  calc
    injectiveMoment H raw5464 = injectiveMoment H raw5464step0 := by
      have heq : raw5464step0 = -raw5464 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5464).symm
    injectiveMoment H raw5464step0 = injectiveMoment H raw5464step1 := by
      have heq : raw5464step1 = (fun i j => raw5464step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5464step0 permutation8 permutation3
    _ = injectiveMoment H node34 := by rfl

def raw5465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5465 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5465 = injectiveMoment H node722 := by
  rfl

def raw5466 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5466 = injectiveMoment H node235 := by
  rfl

def raw5467 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![1, 1, -2], ![1, 0, -1]]

def raw5467step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5467 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5467 = injectiveMoment H node235 := by
  calc
    injectiveMoment H raw5467 = injectiveMoment H raw5467step0 := by
      have heq : raw5467step0 = (fun i j => raw5467 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5467 permutation10 permutation3
    _ = injectiveMoment H node235 := by rfl

def raw5468 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![2, 1, -3]]

def raw5468step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -3, 2], ![-2, -1, 3]]

def raw5468step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

theorem canonical5468 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5468 = injectiveMoment H node39 := by
  calc
    injectiveMoment H raw5468 = injectiveMoment H raw5468step0 := by
      have heq : raw5468step0 = -raw5468 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5468).symm
    injectiveMoment H raw5468step0 = injectiveMoment H raw5468step1 := by
      have heq : raw5468step1 = (fun i j => raw5468step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5468step0 permutation8 permutation3
    _ = injectiveMoment H node39 := by rfl

def raw5469 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 4, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5469 = injectiveMoment H node236 := by
  rfl

def raw5470 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 4, -3], ![2, 0, -2]]

def raw5470step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-4, 4, 0], ![5, -3, -2]]

def raw5470step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

theorem canonical5470 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5470 = injectiveMoment H node29 := by
  calc
    injectiveMoment H raw5470 = injectiveMoment H raw5470step0 := by
      have heq : raw5470step0 = raw5470.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5470).symm
    injectiveMoment H raw5470step0 = injectiveMoment H raw5470step1 := by
      have heq : raw5470step1 = (fun i j => raw5470step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5470step0 permutation8 permutation8
    _ = injectiveMoment H node29 := by rfl

def raw5471 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5471 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5471 = injectiveMoment H node721 := by
  calc
    injectiveMoment H raw5471 = injectiveMoment H raw5471step0 := by
      have heq : raw5471step0 = (fun i j => raw5471 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5471 permutation39 permutation3
    _ = injectiveMoment H node721 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
