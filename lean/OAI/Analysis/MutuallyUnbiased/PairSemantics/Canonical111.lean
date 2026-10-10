import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3552step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3552step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

theorem canonical3552 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3552 = injectiveMoment H node2754 := by
  calc
    injectiveMoment H raw3552 = injectiveMoment H raw3552step0 := by
      have heq : raw3552step0 = -raw3552 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3552).symm
    injectiveMoment H raw3552step0 = injectiveMoment H raw3552step1 := by
      have heq : raw3552step1 = (fun i j => raw3552step0 (permutation76 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3552step0 permutation76 permutation16
    _ = injectiveMoment H node2754 := by rfl

def raw3553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3553step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, 0, -3, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3553step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

theorem canonical3553 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3553 = injectiveMoment H node2764 := by
  calc
    injectiveMoment H raw3553 = injectiveMoment H raw3553step0 := by
      have heq : raw3553step0 = -raw3553 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3553).symm
    injectiveMoment H raw3553step0 = injectiveMoment H raw3553step1 := by
      have heq : raw3553step1 = (fun i j => raw3553step0 (permutation76 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3553step0 permutation76 permutation16
    _ = injectiveMoment H node2764 := by rfl

def raw3554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3554step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical3554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3554 = injectiveMoment H node2039 := by
  calc
    injectiveMoment H raw3554 = injectiveMoment H raw3554step0 := by
      have heq : raw3554step0 = (fun i j => raw3554 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3554 permutation39 permutation9
    _ = injectiveMoment H node2039 := by rfl

def raw3555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3555step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical3555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3555 = injectiveMoment H node2040 := by
  calc
    injectiveMoment H raw3555 = injectiveMoment H raw3555step0 := by
      have heq : raw3555step0 = (fun i j => raw3555 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3555 permutation39 permutation9
    _ = injectiveMoment H node2040 := by rfl

def raw3556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3556step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical3556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3556 = injectiveMoment H node2041 := by
  calc
    injectiveMoment H raw3556 = injectiveMoment H raw3556step0 := by
      have heq : raw3556step0 = (fun i j => raw3556 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3556 permutation39 permutation9
    _ = injectiveMoment H node2041 := by rfl

def raw3557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical3557 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3557 = injectiveMoment H node2042 := by
  calc
    injectiveMoment H raw3557 = injectiveMoment H raw3557step0 := by
      have heq : raw3557step0 = (fun i j => raw3557 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3557 permutation39 permutation9
    _ = injectiveMoment H node2042 := by rfl

def raw3558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -2, 3, -3]]

def raw3558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, -2, 3], ![2, 0, 1, -3]]

def raw3558step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical3558 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3558 = injectiveMoment H node791 := by
  calc
    injectiveMoment H raw3558 = injectiveMoment H raw3558step0 := by
      have heq : raw3558step0 = raw3558.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3558).symm
    injectiveMoment H raw3558step0 = injectiveMoment H raw3558step1 := by
      have heq : raw3558step1 = (fun i j => raw3558step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3558step0 permutation22 permutation17
    _ = injectiveMoment H node791 := by rfl

def raw3559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

theorem canonical3559 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3559 = injectiveMoment H node2047 := by
  rfl

def raw3560 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw3560step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, 0, -2, 3]]

def raw3560step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical3560 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3560 = injectiveMoment H node1657 := by
  calc
    injectiveMoment H raw3560 = injectiveMoment H raw3560step0 := by
      have heq : raw3560step0 = -raw3560 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3560).symm
    injectiveMoment H raw3560step0 = injectiveMoment H raw3560step1 := by
      have heq : raw3560step1 = (fun i j => raw3560step0 (permutation145 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3560step0 permutation145 permutation21
    _ = injectiveMoment H node1657 := by rfl

def raw3561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3561step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, 0, -1, 2]]

def raw3561step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3561 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3561 = injectiveMoment H node2013 := by
  calc
    injectiveMoment H raw3561 = injectiveMoment H raw3561step0 := by
      have heq : raw3561step0 = -raw3561 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3561).symm
    injectiveMoment H raw3561step0 = injectiveMoment H raw3561step1 := by
      have heq : raw3561step1 = (fun i j => raw3561step0 (permutation33 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3561step0 permutation33 permutation30
    _ = injectiveMoment H node2013 := by rfl

def raw3562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical3562 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3562 = injectiveMoment H node1752 := by
  calc
    injectiveMoment H raw3562 = injectiveMoment H raw3562step0 := by
      have heq : raw3562step0 = (fun i j => raw3562 (permutation122 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3562 permutation122 permutation19
    _ = injectiveMoment H node1752 := by rfl

def raw3563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3563step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical3563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3563 = injectiveMoment H node1507 := by
  calc
    injectiveMoment H raw3563 = injectiveMoment H raw3563step0 := by
      have heq : raw3563step0 = (fun i j => raw3563 (permutation125 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3563 permutation125 permutation29
    _ = injectiveMoment H node1507 := by rfl

def raw3564 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical3564 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3564 = injectiveMoment H node2048 := by
  rfl

def raw3565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3565step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical3565 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3565 = injectiveMoment H node1749 := by
  calc
    injectiveMoment H raw3565 = injectiveMoment H raw3565step0 := by
      have heq : raw3565step0 = (fun i j => raw3565 (permutation148 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3565 permutation148 permutation29
    _ = injectiveMoment H node1749 := by rfl

def raw3566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, -1, -1, 1]]

def raw3566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical3566 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3566 = injectiveMoment H node2048 := by
  calc
    injectiveMoment H raw3566 = injectiveMoment H raw3566step0 := by
      have heq : raw3566step0 = (fun i j => raw3566 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3566 permutation34 permutation9
    _ = injectiveMoment H node2048 := by rfl

def raw3567 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3567step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, -1, 2], ![2, 0, 0, -2]]

def raw3567step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical3567 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3567 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw3567 = injectiveMoment H raw3567step0 := by
      have heq : raw3567step0 = raw3567.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3567).symm
    injectiveMoment H raw3567step0 = injectiveMoment H raw3567step1 := by
      have heq : raw3567step1 = (fun i j => raw3567step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3567step0 permutation22 permutation17
    _ = injectiveMoment H node1027 := by rfl

def raw3568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3568step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical3568 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3568 = injectiveMoment H node1800 := by
  calc
    injectiveMoment H raw3568 = injectiveMoment H raw3568step0 := by
      have heq : raw3568step0 = (fun i j => raw3568 (permutation123 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3568 permutation123 permutation19
    _ = injectiveMoment H node1800 := by rfl

def raw3569 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

theorem canonical3569 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3569 = injectiveMoment H node2049 := by
  rfl

def raw3570 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3570step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 1, -2, 2]]

def raw3570step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical3570 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3570 = injectiveMoment H node1776 := by
  calc
    injectiveMoment H raw3570 = injectiveMoment H raw3570step0 := by
      have heq : raw3570step0 = -raw3570 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3570).symm
    injectiveMoment H raw3570step0 = injectiveMoment H raw3570step1 := by
      have heq : raw3570step1 = (fun i j => raw3570step0 (permutation140 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3570step0 permutation140 permutation21
    _ = injectiveMoment H node1776 := by rfl

def raw3571 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3571step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, -1, 1]]

def raw3571step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3571 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3571 = injectiveMoment H node2629 := by
  calc
    injectiveMoment H raw3571 = injectiveMoment H raw3571step0 := by
      have heq : raw3571step0 = -raw3571 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3571).symm
    injectiveMoment H raw3571step0 = injectiveMoment H raw3571step1 := by
      have heq : raw3571step1 = (fun i j => raw3571step0 (permutation149 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3571step0 permutation149 permutation22
    _ = injectiveMoment H node2629 := by rfl

def raw3572 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3572step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 2, -1, 0], ![-1, 0, 1, 0]]

def raw3572step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3572 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3572 = injectiveMoment H node2015 := by
  calc
    injectiveMoment H raw3572 = injectiveMoment H raw3572step0 := by
      have heq : raw3572step0 = -raw3572 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3572).symm
    injectiveMoment H raw3572step0 = injectiveMoment H raw3572step1 := by
      have heq : raw3572step1 = (fun i j => raw3572step0 (permutation38 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3572step0 permutation38 permutation30
    _ = injectiveMoment H node2015 := by rfl

def raw3573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

theorem canonical3573 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3573 = injectiveMoment H node2050 := by
  rfl

def raw3574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3574step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3574step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical3574 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3574 = injectiveMoment H node2613 := by
  calc
    injectiveMoment H raw3574 = injectiveMoment H raw3574step0 := by
      have heq : raw3574step0 = -raw3574 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3574).symm
    injectiveMoment H raw3574step0 = injectiveMoment H raw3574step1 := by
      have heq : raw3574step1 = (fun i j => raw3574step0 (permutation83 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3574step0 permutation83 permutation23
    _ = injectiveMoment H node2613 := by rfl

def raw3575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-1, 2, 0, -1], ![-1, 0, 1, 0]]

def raw3575step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical3575 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3575 = injectiveMoment H node1704 := by
  calc
    injectiveMoment H raw3575 = injectiveMoment H raw3575step0 := by
      have heq : raw3575step0 = -raw3575 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3575).symm
    injectiveMoment H raw3575step0 = injectiveMoment H raw3575step1 := by
      have heq : raw3575step1 = (fun i j => raw3575step0 (permutation82 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3575step0 permutation82 permutation23
    _ = injectiveMoment H node1704 := by rfl

def raw3576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3576step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 0, 0]]

def raw3576step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical3576 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3576 = injectiveMoment H node1698 := by
  calc
    injectiveMoment H raw3576 = injectiveMoment H raw3576step0 := by
      have heq : raw3576step0 = -raw3576 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3576).symm
    injectiveMoment H raw3576step0 = injectiveMoment H raw3576step1 := by
      have heq : raw3576step1 = (fun i j => raw3576step0 (permutation84 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3576step0 permutation84 permutation23
    _ = injectiveMoment H node1698 := by rfl

def raw3577 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw3577step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, 2, -1], ![2, 0, -3, 1]]

def raw3577step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical3577 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3577 = injectiveMoment H node1235 := by
  calc
    injectiveMoment H raw3577 = injectiveMoment H raw3577step0 := by
      have heq : raw3577step0 = raw3577.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3577).symm
    injectiveMoment H raw3577step0 = injectiveMoment H raw3577step1 := by
      have heq : raw3577step1 = (fun i j => raw3577step0 (permutation22 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3577step0 permutation22 permutation16
    _ = injectiveMoment H node1235 := by rfl

def raw3578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

theorem canonical3578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3578 = injectiveMoment H node2051 := by
  rfl

def raw3579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

theorem canonical3579 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3579 = injectiveMoment H node2052 := by
  rfl

def raw3580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem canonical3580 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3580 = injectiveMoment H node2053 := by
  rfl

def raw3581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem canonical3581 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3581 = injectiveMoment H node2054 := by
  rfl

def raw3582 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -2, 2]]

def raw3582step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, 3, -2], ![2, 0, -4, 2]]

def raw3582step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical3582 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3582 = injectiveMoment H node1192 := by
  calc
    injectiveMoment H raw3582 = injectiveMoment H raw3582step0 := by
      have heq : raw3582step0 = raw3582.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3582).symm
    injectiveMoment H raw3582step0 = injectiveMoment H raw3582step1 := by
      have heq : raw3582step1 = (fun i j => raw3582step0 (permutation22 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3582step0 permutation22 permutation16
    _ = injectiveMoment H node1192 := by rfl

def raw3583 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw3583step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -1, -1, 2], ![2, 0, 2, -4]]

def raw3583step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical3583 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3583 = injectiveMoment H node1234 := by
  calc
    injectiveMoment H raw3583 = injectiveMoment H raw3583step0 := by
      have heq : raw3583step0 = raw3583.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3583).symm
    injectiveMoment H raw3583step0 = injectiveMoment H raw3583step1 := by
      have heq : raw3583step1 = (fun i j => raw3583step0 (permutation22 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3583step0 permutation22 permutation15
    _ = injectiveMoment H node1234 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
