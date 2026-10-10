import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8736 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8736 = injectiveMoment H node1404 := by
  calc
    injectiveMoment H raw8736 = injectiveMoment H raw8736step0 := by
      have heq : raw8736step0 = (fun i j => raw8736 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8736 permutation258 permutation3
    _ = injectiveMoment H node1404 := by rfl

def raw8737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8737 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8737 = injectiveMoment H node1886 := by
  calc
    injectiveMoment H raw8737 = injectiveMoment H raw8737step0 := by
      have heq : raw8737step0 = (fun i j => raw8737 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8737 permutation262 permutation3
    _ = injectiveMoment H node1886 := by rfl

def raw8738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8738 = injectiveMoment H node2470 := by
  calc
    injectiveMoment H raw8738 = injectiveMoment H raw8738step0 := by
      have heq : raw8738step0 = (fun i j => raw8738 (permutation399 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8738 permutation399 permutation4
    _ = injectiveMoment H node2470 := by rfl

def raw8739 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8739 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8739 = injectiveMoment H node1430 := by
  calc
    injectiveMoment H raw8739 = injectiveMoment H raw8739step0 := by
      have heq : raw8739step0 = (fun i j => raw8739 (permutation334 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8739 permutation334 permutation4
    _ = injectiveMoment H node1430 := by rfl

def raw8740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8740 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8740 = injectiveMoment H node1429 := by
  calc
    injectiveMoment H raw8740 = injectiveMoment H raw8740step0 := by
      have heq : raw8740step0 = (fun i j => raw8740 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8740 permutation308 permutation3
    _ = injectiveMoment H node1429 := by rfl

def raw8741 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def raw8741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8741 = injectiveMoment H node2100 := by
  calc
    injectiveMoment H raw8741 = injectiveMoment H raw8741step0 := by
      have heq : raw8741step0 = -raw8741 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8741).symm
    injectiveMoment H raw8741step0 = injectiveMoment H raw8741step1 := by
      have heq : raw8741step1 = (fun i j => raw8741step0 (permutation244 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8741step0 permutation244 permutation8
    _ = injectiveMoment H node2100 := by rfl

def raw8742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def raw8742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![-2, 0, 2]]

def raw8742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

theorem canonical8742 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8742 = injectiveMoment H node2097 := by
  calc
    injectiveMoment H raw8742 = injectiveMoment H raw8742step0 := by
      have heq : raw8742step0 = -raw8742 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8742).symm
    injectiveMoment H raw8742step0 = injectiveMoment H raw8742step1 := by
      have heq : raw8742step1 = (fun i j => raw8742step0 (permutation358 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8742step0 permutation358 permutation3
    _ = injectiveMoment H node2097 := by rfl

def raw8743 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def raw8743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem canonical8743 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8743 = injectiveMoment H node1865 := by
  calc
    injectiveMoment H raw8743 = injectiveMoment H raw8743step0 := by
      have heq : raw8743step0 = (fun i j => raw8743 (permutation373 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8743 permutation373 permutation3
    _ = injectiveMoment H node1865 := by rfl

def raw8744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3], ![0, 3, -3]]

def raw8744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![0, 3, -3]]

def raw8744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical8744 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8744 = injectiveMoment H node883 := by
  calc
    injectiveMoment H raw8744 = injectiveMoment H raw8744step0 := by
      have hz : ∀ j, raw8744 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8744step0 = (fun i j => raw8744 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8744 permutation241 hz
    injectiveMoment H raw8744step0 = injectiveMoment H raw8744step1 := by
      have heq : raw8744step1 = (fun i j => raw8744step0 (permutation105 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8744step0 permutation105 permutation3
    _ = injectiveMoment H node883 := by rfl

def raw8745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2], ![0, 3, -3]]

def raw8745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical8745 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8745 = injectiveMoment H node2140 := by
  calc
    injectiveMoment H raw8745 = injectiveMoment H raw8745step0 := by
      have heq : raw8745step0 = (fun i j => raw8745 (permutation263 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8745 permutation263 permutation3
    _ = injectiveMoment H node2140 := by rfl

def raw8746 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3], ![1, 2, -3]]

def raw8746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8746 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8746 = injectiveMoment H node1405 := by
  calc
    injectiveMoment H raw8746 = injectiveMoment H raw8746step0 := by
      have heq : raw8746step0 = (fun i j => raw8746 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8746 permutation258 permutation3
    _ = injectiveMoment H node1405 := by rfl

def raw8747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3], ![0, 3, -3]]

def raw8747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8747 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8747 = injectiveMoment H node1887 := by
  calc
    injectiveMoment H raw8747 = injectiveMoment H raw8747step0 := by
      have heq : raw8747step0 = (fun i j => raw8747 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8747 permutation262 permutation3
    _ = injectiveMoment H node1887 := by rfl

def raw8748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 2, -2]]

def raw8748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8748 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8748 = injectiveMoment H node2139 := by
  calc
    injectiveMoment H raw8748 = injectiveMoment H raw8748step0 := by
      have heq : raw8748step0 = (fun i j => raw8748 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8748 permutation262 permutation3
    _ = injectiveMoment H node2139 := by rfl

def raw8749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, 3, -2]]

def raw8749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8749 = injectiveMoment H node2471 := by
  calc
    injectiveMoment H raw8749 = injectiveMoment H raw8749step0 := by
      have heq : raw8749step0 = (fun i j => raw8749 (permutation398 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8749 permutation398 permutation4
    _ = injectiveMoment H node2471 := by rfl

def raw8750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-3, 2, 1]]

def raw8750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![3, -2, -1]]

def raw8750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8750 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw8750 = injectiveMoment H raw8750step0 := by
      have heq : raw8750step0 = -raw8750 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8750).symm
    injectiveMoment H raw8750step0 = injectiveMoment H raw8750step1 := by
      have heq : raw8750step1 = (fun i j => raw8750step0 (permutation316 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8750step0 permutation316 permutation8
    _ = injectiveMoment H node2469 := by rfl

def raw8751 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![-3, 1, 2]]

def raw8751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8751 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8751 = injectiveMoment H node1430 := by
  calc
    injectiveMoment H raw8751 = injectiveMoment H raw8751step0 := by
      have heq : raw8751step0 = (fun i j => raw8751 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8751 permutation308 permutation3
    _ = injectiveMoment H node1430 := by rfl

def raw8752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, -1, 4], ![1, 2, -3]]

def raw8752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8752 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8752 = injectiveMoment H node1384 := by
  calc
    injectiveMoment H raw8752 = injectiveMoment H raw8752step0 := by
      have heq : raw8752step0 = (fun i j => raw8752 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8752 permutation258 permutation3
    _ = injectiveMoment H node1384 := by rfl

def raw8753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 1, -2]]

def raw8753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![3, 0, -3], ![-1, -1, 2]]

def raw8753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8753 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8753 = injectiveMoment H node2657 := by
  calc
    injectiveMoment H raw8753 = injectiveMoment H raw8753step0 := by
      have heq : raw8753step0 = -raw8753 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8753).symm
    injectiveMoment H raw8753step0 = injectiveMoment H raw8753step1 := by
      have heq : raw8753step1 = (fun i j => raw8753step0 (permutation348 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8753step0 permutation348 permutation5
    _ = injectiveMoment H node2657 := by rfl

def raw8754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -2, 4], ![0, 3, -3]]

def raw8754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8754 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8754 = injectiveMoment H node1540 := by
  calc
    injectiveMoment H raw8754 = injectiveMoment H raw8754step0 := by
      have heq : raw8754step0 = (fun i j => raw8754 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8754 permutation262 permutation3
    _ = injectiveMoment H node1540 := by rfl

def raw8755 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 2, -2]]

def raw8755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8755 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8755 = injectiveMoment H node1885 := by
  calc
    injectiveMoment H raw8755 = injectiveMoment H raw8755step0 := by
      have heq : raw8755step0 = (fun i j => raw8755 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8755 permutation262 permutation3
    _ = injectiveMoment H node1885 := by rfl

def raw8756 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8756 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8756 = injectiveMoment H node2474 := by
  calc
    injectiveMoment H raw8756 = injectiveMoment H raw8756step0 := by
      have heq : raw8756step0 = (fun i j => raw8756 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8756 permutation294 permutation3
    _ = injectiveMoment H node2474 := by rfl

def raw8757 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 2, -1]]

def raw8757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8757 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8757 = injectiveMoment H node2669 := by
  calc
    injectiveMoment H raw8757 = injectiveMoment H raw8757step0 := by
      have heq : raw8757step0 = (fun i j => raw8757 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8757 permutation294 permutation3
    _ = injectiveMoment H node2669 := by rfl

def raw8758 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1]]

def raw8758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1]]

def raw8758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8758 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8758 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw8758 = injectiveMoment H raw8758step0 := by
      have heq : raw8758step0 = -raw8758 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8758).symm
    injectiveMoment H raw8758step0 = injectiveMoment H raw8758step1 := by
      have heq : raw8758step1 = (fun i j => raw8758step0 (permutation318 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8758step0 permutation318 permutation8
    _ = injectiveMoment H node2469 := by rfl

def raw8759 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2]]

def raw8759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2]]

def raw8759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8759 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8759 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw8759 = injectiveMoment H raw8759step0 := by
      have heq : raw8759step0 = -raw8759 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8759).symm
    injectiveMoment H raw8759step0 = injectiveMoment H raw8759step1 := by
      have heq : raw8759step1 = (fun i j => raw8759step0 (permutation347 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8759step0 permutation347 permutation6
    _ = injectiveMoment H node2469 := by rfl

def raw8760 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 0, 3]]

def raw8760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8760 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8760 = injectiveMoment H node2657 := by
  calc
    injectiveMoment H raw8760 = injectiveMoment H raw8760step0 := by
      have heq : raw8760step0 = -raw8760 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8760).symm
    injectiveMoment H raw8760step0 = injectiveMoment H raw8760step1 := by
      have heq : raw8760step1 = (fun i j => raw8760step0 (permutation282 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8760step0 permutation282 permutation5
    _ = injectiveMoment H node2657 := by rfl

def raw8761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, -1, 3], ![-1, 2, -1], ![2, -1, -1]]

def raw8761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical8761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8761 = injectiveMoment H node1866 := by
  calc
    injectiveMoment H raw8761 = injectiveMoment H raw8761step0 := by
      have heq : raw8761step0 = (fun i j => raw8761 (permutation248 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8761 permutation248 permutation3
    _ = injectiveMoment H node1866 := by rfl

def raw8762 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1]]

def raw8762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8762 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8762 = injectiveMoment H node2666 := by
  calc
    injectiveMoment H raw8762 = injectiveMoment H raw8762step0 := by
      have heq : raw8762step0 = (fun i j => raw8762 (permutation316 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8762 permutation316 permutation6
    _ = injectiveMoment H node2666 := by rfl

def raw8763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0]]

def raw8763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1], ![-2, 2, 0]]

def raw8763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

theorem canonical8763 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8763 = injectiveMoment H node2097 := by
  calc
    injectiveMoment H raw8763 = injectiveMoment H raw8763step0 := by
      have heq : raw8763step0 = -raw8763 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8763).symm
    injectiveMoment H raw8763step0 = injectiveMoment H raw8763step1 := by
      have heq : raw8763step1 = (fun i j => raw8763step0 (permutation356 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8763step0 permutation356 permutation4
    _ = injectiveMoment H node2097 := by rfl

def raw8764 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2]]

def raw8764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8764 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8764 = injectiveMoment H node2661 := by
  calc
    injectiveMoment H raw8764 = injectiveMoment H raw8764step0 := by
      have heq : raw8764step0 = (fun i j => raw8764 (permutation269 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8764 permutation269 permutation5
    _ = injectiveMoment H node2661 := by rfl

def raw8765 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -2, 3], ![2, 0, -2]]

def raw8765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical8765 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8765 = injectiveMoment H node1853 := by
  calc
    injectiveMoment H raw8765 = injectiveMoment H raw8765step0 := by
      have heq : raw8765step0 = (fun i j => raw8765 (permutation268 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8765 permutation268 permutation5
    _ = injectiveMoment H node1853 := by rfl

def raw8766 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1]]

def raw8766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![-2, 1, 1]]

def raw8766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8766 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8766 = injectiveMoment H node2100 := by
  calc
    injectiveMoment H raw8766 = injectiveMoment H raw8766step0 := by
      have heq : raw8766step0 = -raw8766 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8766).symm
    injectiveMoment H raw8766step0 = injectiveMoment H raw8766step1 := by
      have heq : raw8766step1 = (fun i j => raw8766step0 (permutation246 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8766step0 permutation246 permutation6
    _ = injectiveMoment H node2100 := by rfl

def raw8767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![-2, -1, 3]]

def raw8767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8767 = injectiveMoment H node2463 := by
  calc
    injectiveMoment H raw8767 = injectiveMoment H raw8767step0 := by
      have heq : raw8767step0 = (fun i j => raw8767 (permutation319 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8767 permutation319 permutation5
    _ = injectiveMoment H node2463 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
