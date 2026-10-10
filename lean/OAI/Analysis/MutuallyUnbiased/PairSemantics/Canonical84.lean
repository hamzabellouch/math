import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2688 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]

def raw2688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2688 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2688 = injectiveMoment H node538 := by
  calc
    injectiveMoment H raw2688 = injectiveMoment H raw2688step0 := by
      have heq : raw2688step0 = (fun i j => raw2688 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2688 permutation35 permutation3
    _ = injectiveMoment H node538 := by rfl

def raw2689 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw2689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw2689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2689 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2689 = injectiveMoment H node374 := by
  calc
    injectiveMoment H raw2689 = injectiveMoment H raw2689step0 := by
      have heq : raw2689step0 = -raw2689 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2689).symm
    injectiveMoment H raw2689step0 = injectiveMoment H raw2689step1 := by
      have heq : raw2689step1 = (fun i j => raw2689step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2689step0 permutation41 permutation8
    _ = injectiveMoment H node374 := by rfl

def raw2690 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw2690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw2690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2690 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2690 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw2690 = injectiveMoment H raw2690step0 := by
      have heq : raw2690step0 = -raw2690 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2690).symm
    injectiveMoment H raw2690step0 = injectiveMoment H raw2690step1 := by
      have heq : raw2690step1 = (fun i j => raw2690step0 (permutation73 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2690step0 permutation73 permutation5
    _ = injectiveMoment H node708 := by rfl

def raw2691 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]

def raw2691step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]

def raw2691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2691 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2691 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw2691 = injectiveMoment H raw2691step0 := by
      have heq : raw2691step0 = -raw2691 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2691).symm
    injectiveMoment H raw2691step0 = injectiveMoment H raw2691step1 := by
      have heq : raw2691step1 = (fun i j => raw2691step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2691step0 permutation20 permutation5
    _ = injectiveMoment H node226 := by rfl

def raw2692 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]

def raw2692step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw2692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical2692 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2692 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw2692 = injectiveMoment H raw2692step0 := by
      have heq : raw2692step0 = -raw2692 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2692).symm
    injectiveMoment H raw2692step0 = injectiveMoment H raw2692step1 := by
      have heq : raw2692step1 = (fun i j => raw2692step0 (permutation18 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2692step0 permutation18 permutation5
    _ = injectiveMoment H node229 := by rfl

def raw2693 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]

def raw2693step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw2693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2693 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2693 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2693 = injectiveMoment H raw2693step0 := by
      have heq : raw2693step0 = -raw2693 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2693).symm
    injectiveMoment H raw2693step0 = injectiveMoment H raw2693step1 := by
      have heq : raw2693step1 = (fun i j => raw2693step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2693step0 permutation13 permutation8
    _ = injectiveMoment H node111 := by rfl

def raw2694 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 2, -3], ![2, -3, 1]]

theorem canonical2694 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2694 = injectiveMoment H node160 := by
  rfl

def raw2695 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -3, 1], ![1, 2, -3]]

def raw2695step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 2, -3], ![2, -3, 1]]

theorem canonical2695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2695 = injectiveMoment H node160 := by
  calc
    injectiveMoment H raw2695 = injectiveMoment H raw2695step0 := by
      have heq : raw2695step0 = (fun i j => raw2695 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2695 permutation10 permutation3
    _ = injectiveMoment H node160 := by rfl

def raw2696 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, 1, -2]]

def raw2696step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-2, 2, 0], ![-1, -1, 2]]

def raw2696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2696 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2696 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2696 = injectiveMoment H raw2696step0 := by
      have heq : raw2696step0 = -raw2696 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2696).symm
    injectiveMoment H raw2696step0 = injectiveMoment H raw2696step1 := by
      have heq : raw2696step1 = (fun i j => raw2696step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2696step0 permutation11 permutation8
    _ = injectiveMoment H node111 := by rfl

def raw2697 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def raw2697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]

def raw2697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]

theorem canonical2697 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2697 = injectiveMoment H node353 := by
  calc
    injectiveMoment H raw2697 = injectiveMoment H raw2697step0 := by
      have heq : raw2697step0 = -raw2697 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2697).symm
    injectiveMoment H raw2697step0 = injectiveMoment H raw2697step1 := by
      have heq : raw2697step1 = (fun i j => raw2697step0 (permutation78 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2697step0 permutation78 permutation5
    _ = injectiveMoment H node353 := by rfl

def raw2698 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw2698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw2698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical2698 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2698 = injectiveMoment H node363 := by
  calc
    injectiveMoment H raw2698 = injectiveMoment H raw2698step0 := by
      have heq : raw2698step0 = -raw2698 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2698).symm
    injectiveMoment H raw2698step0 = injectiveMoment H raw2698step1 := by
      have heq : raw2698step1 = (fun i j => raw2698step0 (permutation72 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2698step0 permutation72 permutation5
    _ = injectiveMoment H node363 := by rfl

def raw2699 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]

def raw2699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw2699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical2699 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2699 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw2699 = injectiveMoment H raw2699step0 := by
      have heq : raw2699step0 = -raw2699 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2699).symm
    injectiveMoment H raw2699step0 = injectiveMoment H raw2699step1 := by
      have heq : raw2699step1 = (fun i j => raw2699step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2699step0 permutation19 permutation5
    _ = injectiveMoment H node103 := by rfl

def raw2700 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw2700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw2700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2700 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2700 = injectiveMoment H node372 := by
  calc
    injectiveMoment H raw2700 = injectiveMoment H raw2700step0 := by
      have heq : raw2700step0 = -raw2700 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2700).symm
    injectiveMoment H raw2700step0 = injectiveMoment H raw2700step1 := by
      have heq : raw2700step1 = (fun i j => raw2700step0 (permutation77 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2700step0 permutation77 permutation5
    _ = injectiveMoment H node372 := by rfl

def raw2701 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]

def raw2701step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 1, 0], ![-2, 1, 1]]

def raw2701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical2701 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2701 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw2701 = injectiveMoment H raw2701step0 := by
      have heq : raw2701step0 = -raw2701 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2701).symm
    injectiveMoment H raw2701step0 = injectiveMoment H raw2701step1 := by
      have heq : raw2701step1 = (fun i j => raw2701step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2701step0 permutation12 permutation8
    _ = injectiveMoment H node109 := by rfl

def raw2702 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 1, -2], ![2, -3, 1]]

def raw2702step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, -1, 2], ![-2, 3, -1]]

def raw2702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 2, -3], ![2, -3, 1]]

theorem canonical2702 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2702 = injectiveMoment H node160 := by
  calc
    injectiveMoment H raw2702 = injectiveMoment H raw2702step0 := by
      have heq : raw2702step0 = -raw2702 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2702).symm
    injectiveMoment H raw2702step0 = injectiveMoment H raw2702step1 := by
      have heq : raw2702step1 = (fun i j => raw2702step0 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2702step0 permutation32 permutation4
    _ = injectiveMoment H node160 := by rfl

def raw2703 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2703 = injectiveMoment H node540 := by
  rfl

def raw2704 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2704 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2704 = injectiveMoment H node161 := by
  rfl

def raw2705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]

def raw2705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2705 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2705 = injectiveMoment H node540 := by
  calc
    injectiveMoment H raw2705 = injectiveMoment H raw2705step0 := by
      have heq : raw2705step0 = (fun i j => raw2705 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2705 permutation35 permutation3
    _ = injectiveMoment H node540 := by rfl

def raw2706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw2706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

theorem canonical2706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2706 = injectiveMoment H node312 := by
  calc
    injectiveMoment H raw2706 = injectiveMoment H raw2706step0 := by
      have heq : raw2706step0 = (fun i j => raw2706 (permutation65 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2706 permutation65 permutation7
    _ = injectiveMoment H node312 := by rfl

def raw2707 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![2, -3, 1], ![1, 0, -1]]

def raw2707step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -4, 3], ![-2, 3, -1], ![-1, 0, 1]]

def raw2707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 3, -4], ![2, -3, 1]]

theorem canonical2707 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2707 = injectiveMoment H node158 := by
  calc
    injectiveMoment H raw2707 = injectiveMoment H raw2707step0 := by
      have heq : raw2707step0 = -raw2707 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2707).symm
    injectiveMoment H raw2707step0 = injectiveMoment H raw2707step1 := by
      have heq : raw2707step1 = (fun i j => raw2707step0 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2707step0 permutation26 permutation4
    _ = injectiveMoment H node158 := by rfl

def raw2708 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![-1, 3, -2], ![1, 0, -1], ![2, 0, -2]]

def raw2708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![1, -3, 2], ![-1, 0, 1], ![-2, 0, 2]]

def raw2708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]

theorem canonical2708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2708 = injectiveMoment H node353 := by
  calc
    injectiveMoment H raw2708 = injectiveMoment H raw2708step0 := by
      have heq : raw2708step0 = -raw2708 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2708).symm
    injectiveMoment H raw2708step0 = injectiveMoment H raw2708step1 := by
      have heq : raw2708step1 = (fun i j => raw2708step0 (permutation102 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2708step0 permutation102 permutation5
    _ = injectiveMoment H node353 := by rfl

def raw2709 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical2709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2709 = injectiveMoment H node541 := by
  rfl

def raw2710 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical2710 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2710 = injectiveMoment H node542 := by
  rfl

def raw2711 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical2711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2711 = injectiveMoment H node543 := by
  rfl

def raw2712 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical2712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2712 = injectiveMoment H node544 := by
  rfl

def raw2713 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical2713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2713 = injectiveMoment H node545 := by
  rfl

def raw2714 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 2, -4]]

def raw2714step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-2, -2, 4]]

def raw2714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

theorem canonical2714 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2714 = injectiveMoment H node140 := by
  calc
    injectiveMoment H raw2714 = injectiveMoment H raw2714step0 := by
      have heq : raw2714step0 = -raw2714 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2714).symm
    injectiveMoment H raw2714step0 = injectiveMoment H raw2714step1 := by
      have heq : raw2714step1 = (fun i j => raw2714step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2714step0 permutation32 permutation3
    _ = injectiveMoment H node140 := by rfl

def raw2715 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]

def raw2715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical2715 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2715 = injectiveMoment H node542 := by
  calc
    injectiveMoment H raw2715 = injectiveMoment H raw2715step0 := by
      have heq : raw2715step0 = (fun i j => raw2715 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2715 permutation35 permutation3
    _ = injectiveMoment H node542 := by rfl

def raw2716 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2716 = injectiveMoment H node546 := by
  rfl

def raw2717 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical2717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2717 = injectiveMoment H node547 := by
  rfl

def raw2718 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical2718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2718 = injectiveMoment H node162 := by
  rfl

def raw2719 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2719 = injectiveMoment H node548 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
