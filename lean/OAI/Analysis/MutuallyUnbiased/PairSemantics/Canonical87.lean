import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2784 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw2784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

theorem canonical2784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2784 = injectiveMoment H node536 := by
  calc
    injectiveMoment H raw2784 = injectiveMoment H raw2784step0 := by
      have heq : raw2784step0 = (fun i j => raw2784 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2784 permutation39 permutation3
    _ = injectiveMoment H node536 := by rfl

def raw2785 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]

def raw2785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw2785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2785 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2785 = injectiveMoment H node377 := by
  calc
    injectiveMoment H raw2785 = injectiveMoment H raw2785step0 := by
      have heq : raw2785step0 = -raw2785 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2785).symm
    injectiveMoment H raw2785step0 = injectiveMoment H raw2785step1 := by
      have heq : raw2785step1 = (fun i j => raw2785step0 (permutation53 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2785step0 permutation53 permutation8
    _ = injectiveMoment H node377 := by rfl

def raw2786 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]

def raw2786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical2786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2786 = injectiveMoment H node537 := by
  calc
    injectiveMoment H raw2786 = injectiveMoment H raw2786step0 := by
      have heq : raw2786step0 = (fun i j => raw2786 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2786 permutation39 permutation3
    _ = injectiveMoment H node537 := by rfl

def raw2787 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw2787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2787 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2787 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw2787 = injectiveMoment H raw2787step0 := by
      have heq : raw2787step0 = (fun i j => raw2787 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2787 permutation39 permutation3
    _ = injectiveMoment H node559 := by rfl

def raw2788 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]

def raw2788step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical2788 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2788 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw2788 = injectiveMoment H raw2788step0 := by
      have heq : raw2788step0 = (fun i j => raw2788 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2788 permutation11 permutation3
    _ = injectiveMoment H node168 := by rfl

def raw2789 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]

def raw2789step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical2789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2789 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw2789 = injectiveMoment H raw2789step0 := by
      have hz : ∀ j, raw2789 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2789step0 = (fun i j => raw2789 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2789 permutation80 hz
    _ = injectiveMoment H node176 := by rfl

def raw2790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]

def raw2790step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical2790 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2790 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw2790 = injectiveMoment H raw2790step0 := by
      have hz : ∀ j, raw2790 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2790step0 = (fun i j => raw2790 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2790 permutation80 hz
    _ = injectiveMoment H node177 := by rfl

def raw2791 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]

def raw2791step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical2791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2791 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw2791 = injectiveMoment H raw2791step0 := by
      have hz : ∀ j, raw2791 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2791step0 = (fun i j => raw2791 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2791 permutation80 hz
    _ = injectiveMoment H node180 := by rfl

def raw2792 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw2792step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2792 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2792 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw2792 = injectiveMoment H raw2792step0 := by
      have hz : ∀ j, raw2792 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2792step0 = (fun i j => raw2792 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2792 permutation80 hz
    _ = injectiveMoment H node181 := by rfl

def raw2793 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw2793step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw2793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical2793 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2793 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw2793 = injectiveMoment H raw2793step0 := by
      have hz : ∀ j, raw2793 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2793step0 = (fun i j => raw2793 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2793 permutation80 hz
    injectiveMoment H raw2793step0 = injectiveMoment H raw2793step1 := by
      have heq : raw2793step1 = (fun i j => raw2793step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2793step0 permutation12 permutation5
    _ = injectiveMoment H node271 := by rfl

def raw2794 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]

def raw2794step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]

def raw2794step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical2794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2794 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2794 = injectiveMoment H raw2794step0 := by
      have hz : ∀ j, raw2794 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw2794step0 = (fun i j => raw2794 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2794 permutation21 hz
    injectiveMoment H raw2794step0 = injectiveMoment H raw2794step1 := by
      have heq : raw2794step1 = (fun i j => raw2794step0 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2794step0 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

def raw2795 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]

def raw2795step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical2795 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2795 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw2795 = injectiveMoment H raw2795step0 := by
      have hz : ∀ j, raw2795 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw2795step0 = (fun i j => raw2795 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2795 permutation104 hz
    _ = injectiveMoment H node176 := by rfl

def raw2796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical2796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2796 = injectiveMoment H node566 := by
  rfl

def raw2797 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

theorem canonical2797 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2797 = injectiveMoment H node567 := by
  rfl

def raw2798 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical2798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2798 = injectiveMoment H node568 := by
  rfl

def raw2799 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical2799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2799 = injectiveMoment H node569 := by
  rfl

def raw2800 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2800 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2800 = injectiveMoment H node570 := by
  rfl

def raw2801 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw2801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2801 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2801 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw2801 = injectiveMoment H raw2801step0 := by
      have heq : raw2801step0 = (fun i j => raw2801 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2801 permutation34 permutation3
    _ = injectiveMoment H node570 := by rfl

def raw2802 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]

def raw2802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical2802 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2802 = injectiveMoment H node569 := by
  calc
    injectiveMoment H raw2802 = injectiveMoment H raw2802step0 := by
      have heq : raw2802step0 = (fun i j => raw2802 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2802 permutation34 permutation3
    _ = injectiveMoment H node569 := by rfl

def raw2803 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical2803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2803 = injectiveMoment H node176 := by
  rfl

def raw2804 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]

def raw2804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical2804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2804 = injectiveMoment H node542 := by
  calc
    injectiveMoment H raw2804 = injectiveMoment H raw2804step0 := by
      have heq : raw2804step0 = (fun i j => raw2804 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2804 permutation45 permutation3
    _ = injectiveMoment H node542 := by rfl

def raw2805 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]

def raw2805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical2805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2805 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw2805 = injectiveMoment H raw2805step0 := by
      have hz : ∀ j, raw2805 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw2805step0 = (fun i j => raw2805 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2805 permutation104 hz
    _ = injectiveMoment H node177 := by rfl

def raw2806 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![2, -3, 1]]

def raw2806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

theorem canonical2806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2806 = injectiveMoment H node567 := by
  calc
    injectiveMoment H raw2806 = injectiveMoment H raw2806step0 := by
      have heq : raw2806step0 = (fun i j => raw2806 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2806 permutation35 permutation3
    _ = injectiveMoment H node567 := by rfl

def raw2807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical2807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2807 = injectiveMoment H node571 := by
  rfl

def raw2808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical2808 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2808 = injectiveMoment H node572 := by
  rfl

def raw2809 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical2809 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2809 = injectiveMoment H node573 := by
  rfl

def raw2810 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]

def raw2810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical2810 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2810 = injectiveMoment H node572 := by
  calc
    injectiveMoment H raw2810 = injectiveMoment H raw2810step0 := by
      have heq : raw2810step0 = (fun i j => raw2810 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2810 permutation34 permutation3
    _ = injectiveMoment H node572 := by rfl

def raw2811 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical2811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2811 = injectiveMoment H node177 := by
  rfl

def raw2812 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical2812 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2812 = injectiveMoment H node574 := by
  rfl

def raw2813 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical2813 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2813 = injectiveMoment H node575 := by
  rfl

def raw2814 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]

def raw2814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical2814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2814 = injectiveMoment H node575 := by
  calc
    injectiveMoment H raw2814 = injectiveMoment H raw2814step0 := by
      have heq : raw2814step0 = (fun i j => raw2814 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2814 permutation34 permutation3
    _ = injectiveMoment H node575 := by rfl

def raw2815 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![2, -3, 1]]

theorem canonical2815 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2815 = injectiveMoment H node178 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
