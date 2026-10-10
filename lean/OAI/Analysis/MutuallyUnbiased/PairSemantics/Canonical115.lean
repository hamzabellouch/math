import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3680 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3680step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3680step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical3680 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3680 = injectiveMoment H node2491 := by
  calc
    injectiveMoment H raw3680 = injectiveMoment H raw3680step0 := by
      have heq : raw3680step0 = -raw3680 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3680).symm
    injectiveMoment H raw3680step0 = injectiveMoment H raw3680step1 := by
      have heq : raw3680step1 = (fun i j => raw3680step0 (permutation149 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3680step0 permutation149 permutation15
    _ = injectiveMoment H node2491 := by rfl

def raw3681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical3681 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3681 = injectiveMoment H node2060 := by
  rfl

def raw3682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![2, 0, 2, -4]]

def raw3682step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical3682 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3682 = injectiveMoment H node1234 := by
  calc
    injectiveMoment H raw3682 = injectiveMoment H raw3682step0 := by
      have heq : raw3682step0 = (fun i j => raw3682 (permutation16 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3682 permutation16 permutation15
    _ = injectiveMoment H node1234 := by rfl

def raw3683 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem canonical3683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3683 = injectiveMoment H node2061 := by
  rfl

def raw3684 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical3684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3684 = injectiveMoment H node2062 := by
  rfl

def raw3685 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical3685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3685 = injectiveMoment H node2063 := by
  rfl

def raw3686 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw3686step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical3686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3686 = injectiveMoment H node2717 := by
  calc
    injectiveMoment H raw3686 = injectiveMoment H raw3686step0 := by
      have heq : raw3686step0 = (fun i j => raw3686 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3686 permutation60 permutation15
    _ = injectiveMoment H node2717 := by rfl

def raw3687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw3687step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical3687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3687 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw3687 = injectiveMoment H raw3687step0 := by
      have heq : raw3687step0 = (fun i j => raw3687 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3687 permutation16 permutation17
    _ = injectiveMoment H node1079 := by rfl

def raw3688 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw3688step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical3688 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3688 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw3688 = injectiveMoment H raw3688step0 := by
      have heq : raw3688step0 = (fun i j => raw3688 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3688 permutation19 permutation17
    _ = injectiveMoment H node1053 := by rfl

def raw3689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw3689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical3689 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3689 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw3689 = injectiveMoment H raw3689step0 := by
      have heq : raw3689step0 = (fun i j => raw3689 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3689 permutation19 permutation17
    _ = injectiveMoment H node1005 := by rfl

def raw3690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, -1, 2, -3]]

def raw3690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 2, 0, -3]]

def raw3690step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![-1, 1, 2, -2], ![-1, -2, 0, 3]]

def raw3690step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical3690 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3690 = injectiveMoment H node496 := by
  calc
    injectiveMoment H raw3690 = injectiveMoment H raw3690step0 := by
      have heq : raw3690step0 = raw3690.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3690).symm
    injectiveMoment H raw3690step0 = injectiveMoment H raw3690step1 := by
      have heq : raw3690step1 = -raw3690step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3690step0).symm
    injectiveMoment H raw3690step1 = injectiveMoment H raw3690step2 := by
      have heq : raw3690step2 = (fun i j => raw3690step1 (permutation28 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3690step1 permutation28 permutation15
    _ = injectiveMoment H node496 := by rfl

def raw3691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 2, 1, -4]]

def raw3691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-1, 1, 1, -1], ![-1, -2, -1, 4]]

def raw3691step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical3691 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3691 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw3691 = injectiveMoment H raw3691step0 := by
      have heq : raw3691step0 = -raw3691 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3691).symm
    injectiveMoment H raw3691step0 = injectiveMoment H raw3691step1 := by
      have heq : raw3691step1 = (fun i j => raw3691step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3691step0 permutation28 permutation17
    _ = injectiveMoment H node454 := by rfl

def raw3692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw3692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical3692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3692 = injectiveMoment H node1003 := by
  calc
    injectiveMoment H raw3692 = injectiveMoment H raw3692step0 := by
      have heq : raw3692step0 = (fun i j => raw3692 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3692 permutation18 permutation23
    _ = injectiveMoment H node1003 := by rfl

def raw3693 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw3693step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-1, 0, 2, -1], ![-1, -1, -2, 4]]

def raw3693step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical3693 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3693 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw3693 = injectiveMoment H raw3693step0 := by
      have heq : raw3693step0 = -raw3693 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3693).symm
    injectiveMoment H raw3693step0 = injectiveMoment H raw3693step1 := by
      have heq : raw3693step1 = (fun i j => raw3693step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3693step0 permutation31 permutation15
    _ = injectiveMoment H node896 := by rfl

def raw3694 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3694step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3694step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical3694 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3694 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw3694 = injectiveMoment H raw3694step0 := by
      have heq : raw3694step0 = -raw3694 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3694).symm
    injectiveMoment H raw3694step0 = injectiveMoment H raw3694step1 := by
      have heq : raw3694step1 = (fun i j => raw3694step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3694step0 permutation31 permutation15
    _ = injectiveMoment H node939 := by rfl

def raw3695 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3695step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical3695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3695 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw3695 = injectiveMoment H raw3695step0 := by
      have heq : raw3695step0 = (fun i j => raw3695 (permutation17 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3695 permutation17 permutation17
    _ = injectiveMoment H node1047 := by rfl

def raw3696 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw3696step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical3696 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3696 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw3696 = injectiveMoment H raw3696step0 := by
      have heq : raw3696step0 = (fun i j => raw3696 (permutation15 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3696 permutation15 permutation17
    _ = injectiveMoment H node1078 := by rfl

def raw3697 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw3697step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical3697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3697 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw3697 = injectiveMoment H raw3697step0 := by
      have heq : raw3697step0 = (fun i j => raw3697 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3697 permutation16 permutation17
    _ = injectiveMoment H node1078 := by rfl

def raw3698 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3698step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical3698 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3698 = injectiveMoment H node2059 := by
  calc
    injectiveMoment H raw3698 = injectiveMoment H raw3698step0 := by
      have heq : raw3698step0 = (fun i j => raw3698 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3698 permutation39 permutation9
    _ = injectiveMoment H node2059 := by rfl

def raw3699 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical3699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3699 = injectiveMoment H node3203 := by
  rfl

def raw3700 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw3700step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw3700step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical3700 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3700 = injectiveMoment H node2977 := by
  calc
    injectiveMoment H raw3700 = injectiveMoment H raw3700step0 := by
      have heq : raw3700step0 = -raw3700 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3700).symm
    injectiveMoment H raw3700step0 = injectiveMoment H raw3700step1 := by
      have heq : raw3700step1 = (fun i j => raw3700step0 (permutation328 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3700step0 permutation328 permutation17
    _ = injectiveMoment H node2977 := by rfl

def raw3701 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3701step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3701step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical3701 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3701 = injectiveMoment H node2532 := by
  calc
    injectiveMoment H raw3701 = injectiveMoment H raw3701step0 := by
      have heq : raw3701step0 = -raw3701 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3701).symm
    injectiveMoment H raw3701step0 = injectiveMoment H raw3701step1 := by
      have heq : raw3701step1 = (fun i j => raw3701step0 (permutation149 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3701step0 permutation149 permutation15
    _ = injectiveMoment H node2532 := by rfl

def raw3702 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw3702step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, -1, 1, 1], ![-1, 0, -1, 2]]

def raw3702step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical3702 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3702 = injectiveMoment H node2623 := by
  calc
    injectiveMoment H raw3702 = injectiveMoment H raw3702step0 := by
      have heq : raw3702step0 = -raw3702 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3702).symm
    injectiveMoment H raw3702step0 = injectiveMoment H raw3702step1 := by
      have heq : raw3702step1 = (fun i j => raw3702step0 (permutation126 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3702step0 permutation126 permutation15
    _ = injectiveMoment H node2623 := by rfl

def raw3703 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical3703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3703 = injectiveMoment H node2070 := by
  rfl

def raw3704 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3704step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3704 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3704 = injectiveMoment H node2744 := by
  calc
    injectiveMoment H raw3704 = injectiveMoment H raw3704step0 := by
      have heq : raw3704step0 = (fun i j => raw3704 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3704 permutation60 permutation15
    _ = injectiveMoment H node2744 := by rfl

def raw3705 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3705step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3705step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical3705 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3705 = injectiveMoment H node2734 := by
  calc
    injectiveMoment H raw3705 = injectiveMoment H raw3705step0 := by
      have heq : raw3705step0 = -raw3705 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3705).symm
    injectiveMoment H raw3705step0 = injectiveMoment H raw3705step1 := by
      have heq : raw3705step1 = (fun i j => raw3705step0 (permutation49 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3705step0 permutation49 permutation24
    _ = injectiveMoment H node2734 := by rfl

def raw3706 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3706step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3706 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw3706 = injectiveMoment H raw3706step0 := by
      have heq : raw3706step0 = (fun i j => raw3706 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3706 permutation30 permutation24
    _ = injectiveMoment H node1241 := by rfl

def raw3707 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 0, -2, 1], ![1, 1, 1, -3]]

def raw3707step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, 0, 2, -1], ![-1, -1, -1, 3]]

def raw3707step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical3707 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3707 = injectiveMoment H node945 := by
  calc
    injectiveMoment H raw3707 = injectiveMoment H raw3707step0 := by
      have heq : raw3707step0 = -raw3707 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3707).symm
    injectiveMoment H raw3707step0 = injectiveMoment H raw3707step1 := by
      have heq : raw3707step1 = (fun i j => raw3707step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3707step0 permutation31 permutation15
    _ = injectiveMoment H node945 := by rfl

def raw3708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw3708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical3708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3708 = injectiveMoment H node1245 := by
  calc
    injectiveMoment H raw3708 = injectiveMoment H raw3708step0 := by
      have heq : raw3708step0 = -raw3708 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3708).symm
    injectiveMoment H raw3708step0 = injectiveMoment H raw3708step1 := by
      have heq : raw3708step1 = (fun i j => raw3708step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3708step0 permutation28 permutation17
    _ = injectiveMoment H node1245 := by rfl

def raw3709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3709step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw3709step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical3709 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3709 = injectiveMoment H node1262 := by
  calc
    injectiveMoment H raw3709 = injectiveMoment H raw3709step0 := by
      have heq : raw3709step0 = -raw3709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3709).symm
    injectiveMoment H raw3709step0 = injectiveMoment H raw3709step1 := by
      have heq : raw3709step1 = (fun i j => raw3709step0 (permutation11 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3709step0 permutation11 permutation24
    _ = injectiveMoment H node1262 := by rfl

def raw3710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw3710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, -1, 2, 0], ![-1, 0, -1, 2]]

def raw3710step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3710 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3710 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw3710 = injectiveMoment H raw3710step0 := by
      have heq : raw3710step0 = -raw3710 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3710).symm
    injectiveMoment H raw3710step0 = injectiveMoment H raw3710step1 := by
      have heq : raw3710step1 = (fun i j => raw3710step0 (permutation25 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3710step0 permutation25 permutation16
    _ = injectiveMoment H node1009 := by rfl

def raw3711 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3711step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw3711step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3711 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3711 = injectiveMoment H node2584 := by
  calc
    injectiveMoment H raw3711 = injectiveMoment H raw3711step0 := by
      have heq : raw3711step0 = -raw3711 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3711).symm
    injectiveMoment H raw3711step0 = injectiveMoment H raw3711step1 := by
      have heq : raw3711step1 = (fun i j => raw3711step0 (permutation149 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3711step0 permutation149 permutation15
    _ = injectiveMoment H node2584 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
