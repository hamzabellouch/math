import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5824 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![1, 2, 0, -3]]

def raw5824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![2, -2, 0], ![1, 2, -3]]

def raw5824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![-2, 2, 0], ![-1, -2, 3]]

def raw5824step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical5824 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5824 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw5824 = injectiveMoment H raw5824step0 := by
      have heq : raw5824step0 = raw5824.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5824).symm
    injectiveMoment H raw5824step0 = injectiveMoment H raw5824step1 := by
      have heq : raw5824step1 = -raw5824step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5824step0).symm
    injectiveMoment H raw5824step1 = injectiveMoment H raw5824step2 := by
      have heq : raw5824step2 = (fun i j => raw5824step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5824step1 permutation27 permutation5
    _ = injectiveMoment H node177 := by rfl

def raw5825 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical5825 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5825 = injectiveMoment H node2455 := by
  rfl

def raw5826 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5826step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

theorem canonical5826 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5826 = injectiveMoment H node2446 := by
  calc
    injectiveMoment H raw5826 = injectiveMoment H raw5826step0 := by
      have heq : raw5826step0 = (fun i j => raw5826 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5826 permutation33 permutation10
    _ = injectiveMoment H node2446 := by rfl

def raw5827 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5827step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical5827 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5827 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw5827 = injectiveMoment H raw5827step0 := by
      have heq : raw5827step0 = (fun i j => raw5827 (permutation35 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5827 permutation35 permutation10
    _ = injectiveMoment H node2449 := by rfl

def raw5828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw5828step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw5828step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical5828 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5828 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw5828 = injectiveMoment H raw5828step0 := by
      have heq : raw5828step0 = raw5828.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5828).symm
    injectiveMoment H raw5828step0 = injectiveMoment H raw5828step1 := by
      have heq : raw5828step1 = (fun i j => raw5828step0 (permutation22 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5828step0 permutation22 permutation24
    _ = injectiveMoment H node1047 := by rfl

def raw5829 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5829step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical5829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5829 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw5829 = injectiveMoment H raw5829step0 := by
      have heq : raw5829step0 = (fun i j => raw5829 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5829 permutation33 permutation10
    _ = injectiveMoment H node2448 := by rfl

def raw5830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5830step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![2, -1, 0, -1], ![1, 1, -1, -1]]

def raw5830step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, 0, -1, -1], ![-2, 1, 0, 1], ![-1, -1, 1, 1]]

def raw5830step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical5830 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5830 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw5830 = injectiveMoment H raw5830step0 := by
      have heq : raw5830step0 = raw5830.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5830).symm
    injectiveMoment H raw5830step0 = injectiveMoment H raw5830step1 := by
      have heq : raw5830step1 = -raw5830step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5830step0).symm
    injectiveMoment H raw5830step1 = injectiveMoment H raw5830step2 := by
      have heq : raw5830step2 = (fun i j => raw5830step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5830step1 permutation15 permutation24
    _ = injectiveMoment H node1260 := by rfl

def raw5831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![2, -1, -1, 0], ![1, 1, -1, -1]]

def raw5831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical5831 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5831 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw5831 = injectiveMoment H raw5831step0 := by
      have heq : raw5831step0 = raw5831.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5831).symm
    injectiveMoment H raw5831step0 = injectiveMoment H raw5831step1 := by
      have heq : raw5831step1 = (fun i j => raw5831step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5831step0 permutation23 permutation20
    _ = injectiveMoment H node1265 := by rfl

def raw5832 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5832step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![2, -1, 0, -1], ![1, 1, -2, 0]]

def raw5832step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical5832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5832 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw5832 = injectiveMoment H raw5832step0 := by
      have heq : raw5832step0 = raw5832.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5832).symm
    injectiveMoment H raw5832step0 = injectiveMoment H raw5832step1 := by
      have heq : raw5832step1 = (fun i j => raw5832step0 (permutation24 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5832step0 permutation24 permutation30
    _ = injectiveMoment H node1053 := by rfl

def raw5833 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5833step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical5833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5833 = injectiveMoment H node2444 := by
  calc
    injectiveMoment H raw5833 = injectiveMoment H raw5833step0 := by
      have heq : raw5833step0 = (fun i j => raw5833 (permutation35 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5833 permutation35 permutation10
    _ = injectiveMoment H node2444 := by rfl

def raw5834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw5834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![2, 1, -3, 0], ![1, -1, 1, -1]]

def raw5834step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical5834 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5834 = injectiveMoment H node1109 := by
  calc
    injectiveMoment H raw5834 = injectiveMoment H raw5834step0 := by
      have heq : raw5834step0 = raw5834.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5834).symm
    injectiveMoment H raw5834step0 = injectiveMoment H raw5834step1 := by
      have heq : raw5834step1 = (fun i j => raw5834step0 (permutation29 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5834step0 permutation29 permutation19
    _ = injectiveMoment H node1109 := by rfl

def raw5835 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, 2, -2], ![1, 2, -4, 1]]

def raw5835step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![2, 2, -4], ![1, -2, 1]]

def raw5835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![-2, -2, 4], ![-1, 2, -1]]

def raw5835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5835 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5835 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw5835 = injectiveMoment H raw5835step0 := by
      have heq : raw5835step0 = raw5835.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5835).symm
    injectiveMoment H raw5835step0 = injectiveMoment H raw5835step1 := by
      have heq : raw5835step1 = -raw5835step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5835step0).symm
    injectiveMoment H raw5835step1 = injectiveMoment H raw5835step2 := by
      have heq : raw5835step2 = (fun i j => raw5835step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5835step1 permutation21 permutation5
    _ = injectiveMoment H node146 := by rfl

def raw5836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![2, -2, 0, 0], ![1, 1, -1, -1]]

def raw5836step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5836 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw5836 = injectiveMoment H raw5836step0 := by
      have heq : raw5836step0 = raw5836.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5836).symm
    injectiveMoment H raw5836step0 = injectiveMoment H raw5836step1 := by
      have heq : raw5836step1 = (fun i j => raw5836step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5836step0 permutation31 permutation26
    _ = injectiveMoment H node1110 := by rfl

def raw5837 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 1, -2]]

def raw5837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical5837 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5837 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw5837 = injectiveMoment H raw5837step0 := by
      have heq : raw5837step0 = raw5837.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5837).symm
    injectiveMoment H raw5837step0 = injectiveMoment H raw5837step1 := by
      have heq : raw5837step1 = (fun i j => raw5837step0 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5837step0 permutation22 permutation6
    _ = injectiveMoment H node210 := by rfl

def raw5838 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5838step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![2, -1, -1, 0], ![1, 0, 0, -1]]

def raw5838step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical5838 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5838 = injectiveMoment H node1039 := by
  calc
    injectiveMoment H raw5838 = injectiveMoment H raw5838step0 := by
      have heq : raw5838step0 = raw5838.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5838).symm
    injectiveMoment H raw5838step0 = injectiveMoment H raw5838step1 := by
      have heq : raw5838step1 = (fun i j => raw5838step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5838step0 permutation25 permutation18
    _ = injectiveMoment H node1039 := by rfl

def raw5839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![2, -1, 0, -1], ![1, 0, -1, 0]]

def raw5839step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5839 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw5839 = injectiveMoment H raw5839step0 := by
      have heq : raw5839step0 = raw5839.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5839).symm
    injectiveMoment H raw5839step0 = injectiveMoment H raw5839step1 := by
      have heq : raw5839step1 = (fun i j => raw5839step0 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5839step0 permutation25 permutation20
    _ = injectiveMoment H node1044 := by rfl

def raw5840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw5840step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![2, 0, 0, -2], ![1, -1, -1, 1]]

def raw5840step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, -1, -1, 0], ![-2, 0, 0, 2], ![-1, 1, 1, -1]]

def raw5840step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical5840 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5840 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw5840 = injectiveMoment H raw5840step0 := by
      have heq : raw5840step0 = raw5840.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5840).symm
    injectiveMoment H raw5840step0 = injectiveMoment H raw5840step1 := by
      have heq : raw5840step1 = -raw5840step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5840step0).symm
    injectiveMoment H raw5840step1 = injectiveMoment H raw5840step2 := by
      have heq : raw5840step2 = (fun i j => raw5840step1 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5840step1 permutation15 permutation18
    _ = injectiveMoment H node1040 := by rfl

def raw5841 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, 2, -3], ![1, 1, -4, 2]]

def raw5841step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![2, 2, -4], ![1, -3, 2]]

def raw5841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical5841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5841 = injectiveMoment H node106 := by
  calc
    injectiveMoment H raw5841 = injectiveMoment H raw5841step0 := by
      have heq : raw5841step0 = raw5841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5841).symm
    injectiveMoment H raw5841step0 = injectiveMoment H raw5841step1 := by
      have heq : raw5841step1 = (fun i j => raw5841step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5841step0 permutation27 permutation5
    _ = injectiveMoment H node106 := by rfl

def raw5842 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw5842step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![2, -3, 1], ![1, 1, -2]]

def raw5842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5842 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw5842 = injectiveMoment H raw5842step0 := by
      have heq : raw5842step0 = raw5842.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5842).symm
    injectiveMoment H raw5842step0 = injectiveMoment H raw5842step1 := by
      have heq : raw5842step1 = (fun i j => raw5842step0 (permutation29 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5842step0 permutation29 permutation7
    _ = injectiveMoment H node226 := by rfl

def raw5843 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5843step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![2, 0, -2], ![1, -2, 1]]

def raw5843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, 2, -1]]

def raw5843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5843 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5843 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5843 = injectiveMoment H raw5843step0 := by
      have heq : raw5843step0 = raw5843.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5843).symm
    injectiveMoment H raw5843step0 = injectiveMoment H raw5843step1 := by
      have heq : raw5843step1 = -raw5843step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5843step0).symm
    injectiveMoment H raw5843step1 = injectiveMoment H raw5843step2 := by
      have heq : raw5843step2 = (fun i j => raw5843step1 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5843step1 permutation15 permutation6
    _ = injectiveMoment H node203 := by rfl

def raw5844 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 3, -3, 0], ![1, -1, 1, -1]]

def raw5844step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![2, -3, 1], ![1, 0, -1]]

def raw5844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5844 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw5844 = injectiveMoment H raw5844step0 := by
      have heq : raw5844step0 = raw5844.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5844).symm
    injectiveMoment H raw5844step0 = injectiveMoment H raw5844step1 := by
      have heq : raw5844step1 = (fun i j => raw5844step0 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5844step0 permutation19 permutation7
    _ = injectiveMoment H node259 := by rfl

def raw5845 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![1, -1, 2, -2], ![0, 3, -4, 1]]

def raw5845step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![2, 2, -4], ![1, -2, 1]]

def raw5845step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, 1, -3], ![-2, -2, 4], ![-1, 2, -1]]

def raw5845step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

theorem canonical5845 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5845 = injectiveMoment H node132 := by
  calc
    injectiveMoment H raw5845 = injectiveMoment H raw5845step0 := by
      have heq : raw5845step0 = raw5845.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5845).symm
    injectiveMoment H raw5845step0 = injectiveMoment H raw5845step1 := by
      have heq : raw5845step1 = -raw5845step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5845step0).symm
    injectiveMoment H raw5845step1 = injectiveMoment H raw5845step2 := by
      have heq : raw5845step2 = (fun i j => raw5845step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5845step1 permutation21 permutation5
    _ = injectiveMoment H node132 := by rfl

def raw5846 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![1, 0, -2, 1], ![0, 2, 0, -2]]

def raw5846step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![2, -2, 0], ![1, 1, -2]]

def raw5846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, 0, -2], ![-2, 2, 0], ![-1, -1, 2]]

def raw5846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5846 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5846 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5846 = injectiveMoment H raw5846step0 := by
      have heq : raw5846step0 = raw5846.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5846).symm
    injectiveMoment H raw5846step0 = injectiveMoment H raw5846step1 := by
      have heq : raw5846step1 = -raw5846step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5846step0).symm
    injectiveMoment H raw5846step1 = injectiveMoment H raw5846step2 := by
      have heq : raw5846step2 = (fun i j => raw5846step1 (permutation15 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5846step1 permutation15 permutation8
    _ = injectiveMoment H node203 := by rfl

def raw5847 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![1, 0, 2, -3], ![0, 2, -4, 2]]

def raw5847step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![2, 2, -4], ![1, -3, 2]]

def raw5847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

theorem canonical5847 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5847 = injectiveMoment H node102 := by
  calc
    injectiveMoment H raw5847 = injectiveMoment H raw5847step0 := by
      have heq : raw5847step0 = raw5847.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5847).symm
    injectiveMoment H raw5847step0 = injectiveMoment H raw5847step1 := by
      have heq : raw5847step1 = (fun i j => raw5847step0 (permutation29 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5847step0 permutation29 permutation5
    _ = injectiveMoment H node102 := by rfl

def raw5848 : Matrix (Fin 2) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![1, 2, -2, -1]]

def raw5848step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw5848step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5848 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5848 = injectiveMoment H raw5848step0 := by
      have heq : raw5848step0 = raw5848.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5848).symm
    injectiveMoment H raw5848step0 = injectiveMoment H raw5848step1 := by
      have heq : raw5848step1 = (fun i j => raw5848step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5848step0 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5849 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![2, -1, 1, -2], ![-1, 3, -3, 1]]

def raw5849step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, -1, 3], ![2, 1, -3], ![1, -2, 1]]

def raw5849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical5849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5849 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw5849 = injectiveMoment H raw5849step0 := by
      have heq : raw5849step0 = raw5849.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5849).symm
    injectiveMoment H raw5849step0 = injectiveMoment H raw5849step1 := by
      have heq : raw5849step1 = (fun i j => raw5849step0 (permutation16 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5849step0 permutation16 permutation3
    _ = injectiveMoment H node159 := by rfl

def raw5850 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![2, 0, 0, -2], ![-1, 2, -2, 1]]

def raw5850step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![2, 0, -2], ![1, -2, 1]]

def raw5850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5850 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw5850 = injectiveMoment H raw5850step0 := by
      have heq : raw5850step0 = raw5850.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5850).symm
    injectiveMoment H raw5850step0 = injectiveMoment H raw5850step1 := by
      have heq : raw5850step1 = (fun i j => raw5850step0 (permutation30 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5850step0 permutation30 permutation5
    _ = injectiveMoment H node224 := by rfl

def raw5851 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![2, 0, 1, -3], ![-1, 2, -3, 2]]

def raw5851step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![2, 1, -3], ![1, -3, 2]]

def raw5851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical5851 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5851 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw5851 = injectiveMoment H raw5851step0 := by
      have heq : raw5851step0 = raw5851.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5851).symm
    injectiveMoment H raw5851step0 = injectiveMoment H raw5851step1 := by
      have heq : raw5851step1 = (fun i j => raw5851step0 (permutation30 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5851step0 permutation30 permutation5
    _ = injectiveMoment H node103 := by rfl

def raw5852 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw5852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -3, 4]]

def raw5852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5852 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5852 = injectiveMoment H node735 := by
  calc
    injectiveMoment H raw5852 = injectiveMoment H raw5852step0 := by
      have heq : raw5852step0 = -raw5852 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5852).symm
    injectiveMoment H raw5852step0 = injectiveMoment H raw5852step1 := by
      have heq : raw5852step1 = (fun i j => raw5852step0 (permutation150 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5852step0 permutation150 permutation3
    _ = injectiveMoment H node735 := by rfl

def raw5853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical5853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5853 = injectiveMoment H node855 := by
  rfl

def raw5854 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5854 = injectiveMoment H node856 := by
  rfl

def raw5855 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5855 = injectiveMoment H node857 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
