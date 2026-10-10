import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2656 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical2656 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2656 = injectiveMoment H node526 := by
  rfl

def raw2657 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![3, 0, -3]]

def raw2657step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-3, 0, 3]]

def raw2657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2657 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2657 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw2657 = injectiveMoment H raw2657step0 := by
      have heq : raw2657step0 = -raw2657 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2657).symm
    injectiveMoment H raw2657step0 = injectiveMoment H raw2657step1 := by
      have heq : raw2657step1 = (fun i j => raw2657step0 (permutation26 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2657step0 permutation26 permutation5
    _ = injectiveMoment H node196 := by rfl

def raw2658 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]

def raw2658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical2658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2658 = injectiveMoment H node856 := by
  calc
    injectiveMoment H raw2658 = injectiveMoment H raw2658step0 := by
      have heq : raw2658step0 = (fun i j => raw2658 (permutation33 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2658 permutation33 permutation5
    _ = injectiveMoment H node856 := by rfl

def raw2659 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]

def raw2659step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2659 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2659 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw2659 = injectiveMoment H raw2659step0 := by
      have heq : raw2659step0 = (fun i j => raw2659 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2659 permutation9 permutation5
    _ = injectiveMoment H node258 := by rfl

def raw2660 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]

def raw2660step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw2660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2660 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2660 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw2660 = injectiveMoment H raw2660step0 := by
      have heq : raw2660step0 = -raw2660 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2660).symm
    injectiveMoment H raw2660step0 = injectiveMoment H raw2660step1 := by
      have heq : raw2660step1 = (fun i j => raw2660step0 (permutation26 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2660step0 permutation26 permutation5
    _ = injectiveMoment H node167 := by rfl

def raw2661 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 3, -4], ![2, -1, -1]]

def raw2661step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -3, 4], ![-2, 1, 1]]

def raw2661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2661 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2661 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw2661 = injectiveMoment H raw2661step0 := by
      have heq : raw2661step0 = -raw2661 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2661).symm
    injectiveMoment H raw2661step0 = injectiveMoment H raw2661step1 := by
      have heq : raw2661step1 = (fun i j => raw2661step0 (permutation26 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2661step0 permutation26 permutation5
    _ = injectiveMoment H node89 := by rfl

def raw2662 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw2662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw2662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2662 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2662 = injectiveMoment H node862 := by
  calc
    injectiveMoment H raw2662 = injectiveMoment H raw2662step0 := by
      have heq : raw2662step0 = -raw2662 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2662).symm
    injectiveMoment H raw2662step0 = injectiveMoment H raw2662step1 := by
      have heq : raw2662step1 = (fun i j => raw2662step0 (permutation142 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2662step0 permutation142 permutation5
    _ = injectiveMoment H node862 := by rfl

def raw2663 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw2663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw2663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2663 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2663 = injectiveMoment H node645 := by
  calc
    injectiveMoment H raw2663 = injectiveMoment H raw2663step0 := by
      have heq : raw2663step0 = -raw2663 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2663).symm
    injectiveMoment H raw2663step0 = injectiveMoment H raw2663step1 := by
      have heq : raw2663step1 = (fun i j => raw2663step0 (permutation101 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2663step0 permutation101 permutation5
    _ = injectiveMoment H node645 := by rfl

def raw2664 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw2664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw2664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical2664 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2664 = injectiveMoment H node658 := by
  calc
    injectiveMoment H raw2664 = injectiveMoment H raw2664step0 := by
      have heq : raw2664step0 = -raw2664 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2664).symm
    injectiveMoment H raw2664step0 = injectiveMoment H raw2664step1 := by
      have heq : raw2664step1 = (fun i j => raw2664step0 (permutation95 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2664step0 permutation95 permutation5
    _ = injectiveMoment H node658 := by rfl

def raw2665 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw2665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw2665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2665 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2665 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw2665 = injectiveMoment H raw2665step0 := by
      have heq : raw2665step0 = -raw2665 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2665).symm
    injectiveMoment H raw2665step0 = injectiveMoment H raw2665step1 := by
      have heq : raw2665step1 = (fun i j => raw2665step0 (permutation148 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2665step0 permutation148 permutation5
    _ = injectiveMoment H node559 := by rfl

def raw2666 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]

def raw2666step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]

def raw2666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical2666 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2666 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw2666 = injectiveMoment H raw2666step0 := by
      have heq : raw2666step0 = -raw2666 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2666).symm
    injectiveMoment H raw2666step0 = injectiveMoment H raw2666step1 := by
      have heq : raw2666step1 = (fun i j => raw2666step0 (permutation24 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2666step0 permutation24 permutation5
    _ = injectiveMoment H node180 := by rfl

def raw2667 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw2667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2667 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2667 = injectiveMoment H node869 := by
  calc
    injectiveMoment H raw2667 = injectiveMoment H raw2667step0 := by
      have heq : raw2667step0 = (fun i j => raw2667 (permutation49 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2667 permutation49 permutation5
    _ = injectiveMoment H node869 := by rfl

def raw2668 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw2668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2668 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw2668 = injectiveMoment H raw2668step0 := by
      have heq : raw2668step0 = (fun i j => raw2668 (permutation55 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2668 permutation55 permutation5
    _ = injectiveMoment H node872 := by rfl

def raw2669 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical2669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2669 = injectiveMoment H node533 := by
  rfl

def raw2670 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw2670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]

def raw2670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical2670 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2670 = injectiveMoment H node369 := by
  calc
    injectiveMoment H raw2670 = injectiveMoment H raw2670step0 := by
      have heq : raw2670step0 = -raw2670 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2670).symm
    injectiveMoment H raw2670step0 = injectiveMoment H raw2670step1 := by
      have heq : raw2670step1 = (fun i j => raw2670step0 (permutation38 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2670step0 permutation38 permutation8
    _ = injectiveMoment H node369 := by rfl

def raw2671 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw2671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

theorem canonical2671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2671 = injectiveMoment H node364 := by
  calc
    injectiveMoment H raw2671 = injectiveMoment H raw2671step0 := by
      have heq : raw2671step0 = (fun i j => raw2671 (permutation136 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2671 permutation136 permutation7
    _ = injectiveMoment H node364 := by rfl

def raw2672 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw2672step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2672 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2672 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw2672 = injectiveMoment H raw2672step0 := by
      have heq : raw2672step0 = (fun i j => raw2672 (permutation13 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2672 permutation13 permutation5
    _ = injectiveMoment H node261 := by rfl

def raw2673 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]

def raw2673step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical2673 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2673 = injectiveMoment H node105 := by
  calc
    injectiveMoment H raw2673 = injectiveMoment H raw2673step0 := by
      have heq : raw2673step0 = (fun i j => raw2673 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2673 permutation24 permutation7
    _ = injectiveMoment H node105 := by rfl

def raw2674 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

def raw2674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-2, -1, 3]]

def raw2674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical2674 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2674 = injectiveMoment H node528 := by
  calc
    injectiveMoment H raw2674 = injectiveMoment H raw2674step0 := by
      have heq : raw2674step0 = -raw2674 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2674).symm
    injectiveMoment H raw2674step0 = injectiveMoment H raw2674step1 := by
      have heq : raw2674step1 = (fun i j => raw2674step0 (permutation150 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2674step0 permutation150 permutation3
    _ = injectiveMoment H node528 := by rfl

def raw2675 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

theorem canonical2675 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2675 = injectiveMoment H node534 := by
  rfl

def raw2676 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]

def raw2676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]

def raw2676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical2676 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2676 = injectiveMoment H node702 := by
  calc
    injectiveMoment H raw2676 = injectiveMoment H raw2676step0 := by
      have heq : raw2676step0 = -raw2676 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2676).symm
    injectiveMoment H raw2676step0 = injectiveMoment H raw2676step1 := by
      have heq : raw2676step1 = (fun i j => raw2676step0 (permutation79 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2676step0 permutation79 permutation5
    _ = injectiveMoment H node702 := by rfl

def raw2677 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical2677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2677 = injectiveMoment H node535 := by
  rfl

def raw2678 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]

def raw2678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw2678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]

def raw2678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2678 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2678 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw2678 = injectiveMoment H raw2678step0 := by
      have heq : raw2678step0 = -raw2678 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2678).symm
    injectiveMoment H raw2678step0 = injectiveMoment H raw2678step1 := by
      have hz : ∀ j, raw2678step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2678step1 = (fun i j => raw2678step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2678step0 permutation80 hz
    injectiveMoment H raw2678step1 = injectiveMoment H raw2678step2 := by
      have heq : raw2678step2 = (fun i j => raw2678step1 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2678step1 permutation20 permutation5
    _ = injectiveMoment H node226 := by rfl

def raw2679 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]

def raw2679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw2679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw2679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical2679 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2679 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw2679 = injectiveMoment H raw2679step0 := by
      have heq : raw2679step0 = -raw2679 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2679).symm
    injectiveMoment H raw2679step0 = injectiveMoment H raw2679step1 := by
      have hz : ∀ j, raw2679step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2679step1 = (fun i j => raw2679step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2679step0 permutation80 hz
    injectiveMoment H raw2679step1 = injectiveMoment H raw2679step2 := by
      have heq : raw2679step2 = (fun i j => raw2679step1 (permutation18 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2679step1 permutation18 permutation5
    _ = injectiveMoment H node229 := by rfl

def raw2680 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

theorem canonical2680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2680 = injectiveMoment H node536 := by
  rfl

def raw2681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw2681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw2681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2681 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2681 = injectiveMoment H node376 := by
  calc
    injectiveMoment H raw2681 = injectiveMoment H raw2681step0 := by
      have heq : raw2681step0 = -raw2681 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2681).symm
    injectiveMoment H raw2681step0 = injectiveMoment H raw2681step1 := by
      have heq : raw2681step1 = (fun i j => raw2681step0 (permutation45 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2681step0 permutation45 permutation8
    _ = injectiveMoment H node376 := by rfl

def raw2682 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw2682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw2682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2682 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2682 = injectiveMoment H node377 := by
  calc
    injectiveMoment H raw2682 = injectiveMoment H raw2682step0 := by
      have heq : raw2682step0 = -raw2682 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2682).symm
    injectiveMoment H raw2682step0 = injectiveMoment H raw2682step1 := by
      have heq : raw2682step1 = (fun i j => raw2682step0 (permutation51 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2682step0 permutation51 permutation8
    _ = injectiveMoment H node377 := by rfl

def raw2683 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical2683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2683 = injectiveMoment H node537 := by
  rfl

def raw2684 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2684 = injectiveMoment H node538 := by
  rfl

def raw2685 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical2685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2685 = injectiveMoment H node539 := by
  rfl

def raw2686 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]

def raw2686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical2686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2686 = injectiveMoment H node539 := by
  calc
    injectiveMoment H raw2686 = injectiveMoment H raw2686step0 := by
      have heq : raw2686step0 = (fun i j => raw2686 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2686 permutation34 permutation3
    _ = injectiveMoment H node539 := by rfl

def raw2687 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical2687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2687 = injectiveMoment H node159 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
