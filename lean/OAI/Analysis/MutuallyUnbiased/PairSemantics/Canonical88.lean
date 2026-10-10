import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2816 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical2816 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2816 = injectiveMoment H node179 := by
  rfl

def raw2817 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical2817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2817 = injectiveMoment H node180 := by
  rfl

def raw2818 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3]]

def raw2818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2818 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw2818 = injectiveMoment H raw2818step0 := by
      have heq : raw2818step0 = (fun i j => raw2818 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2818 permutation45 permutation3
    _ = injectiveMoment H node559 := by rfl

def raw2819 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]

def raw2819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical2819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2819 = injectiveMoment H node573 := by
  calc
    injectiveMoment H raw2819 = injectiveMoment H raw2819step0 := by
      have heq : raw2819step0 = (fun i j => raw2819 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2819 permutation37 permutation3
    _ = injectiveMoment H node573 := by rfl

def raw2820 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2820 = injectiveMoment H node181 := by
  rfl

def raw2821 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw2821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical2821 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2821 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw2821 = injectiveMoment H raw2821step0 := by
      have heq : raw2821step0 = (fun i j => raw2821 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2821 permutation12 permutation5
    _ = injectiveMoment H node271 := by rfl

def raw2822 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 2, -3], ![1, -2, 1]]

def raw2822step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical2822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2822 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw2822 = injectiveMoment H raw2822step0 := by
      have heq : raw2822step0 = (fun i j => raw2822 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2822 permutation10 permutation3
    _ = injectiveMoment H node180 := by rfl

def raw2823 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]

def raw2823step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

def raw2824 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw2824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical2824 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2824 = injectiveMoment H node547 := by
  calc
    injectiveMoment H raw2824 = injectiveMoment H raw2824step0 := by
      have heq : raw2824step0 = (fun i j => raw2824 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2824 permutation39 permutation3
    _ = injectiveMoment H node547 := by rfl

def raw2825 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]

def raw2825step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical2825 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2825 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw2825 = injectiveMoment H raw2825step0 := by
      have heq : raw2825step0 = (fun i j => raw2825 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2825 permutation11 permutation3
    _ = injectiveMoment H node162 := by rfl

def raw2826 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw2826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2826 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2826 = injectiveMoment H node561 := by
  calc
    injectiveMoment H raw2826 = injectiveMoment H raw2826step0 := by
      have heq : raw2826step0 = (fun i j => raw2826 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2826 permutation39 permutation3
    _ = injectiveMoment H node561 := by rfl

def raw2827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw2827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical2827 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2827 = injectiveMoment H node562 := by
  calc
    injectiveMoment H raw2827 = injectiveMoment H raw2827step0 := by
      have heq : raw2827step0 = (fun i j => raw2827 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2827 permutation39 permutation3
    _ = injectiveMoment H node562 := by rfl

def raw2828 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]

def raw2828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical2828 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2828 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw2828 = injectiveMoment H raw2828step0 := by
      have heq : raw2828step0 = (fun i j => raw2828 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2828 permutation11 permutation3
    _ = injectiveMoment H node169 := by rfl

def raw2829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def raw2829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

theorem canonical2829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2829 = injectiveMoment H node567 := by
  calc
    injectiveMoment H raw2829 = injectiveMoment H raw2829step0 := by
      have heq : raw2829step0 = (fun i j => raw2829 (permutation41 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2829 permutation41 permutation3
    _ = injectiveMoment H node567 := by rfl

def raw2830 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw2830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical2830 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2830 = injectiveMoment H node571 := by
  calc
    injectiveMoment H raw2830 = injectiveMoment H raw2830step0 := by
      have heq : raw2830step0 = (fun i j => raw2830 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2830 permutation39 permutation3
    _ = injectiveMoment H node571 := by rfl

def raw2831 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw2831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical2831 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2831 = injectiveMoment H node572 := by
  calc
    injectiveMoment H raw2831 = injectiveMoment H raw2831step0 := by
      have heq : raw2831step0 = (fun i j => raw2831 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2831 permutation39 permutation3
    _ = injectiveMoment H node572 := by rfl

def raw2832 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw2832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical2832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2832 = injectiveMoment H node573 := by
  calc
    injectiveMoment H raw2832 = injectiveMoment H raw2832step0 := by
      have heq : raw2832step0 = (fun i j => raw2832 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2832 permutation39 permutation3
    _ = injectiveMoment H node573 := by rfl

def raw2833 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]

def raw2833step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical2833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2833 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw2833 = injectiveMoment H raw2833step0 := by
      have heq : raw2833step0 = (fun i j => raw2833 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2833 permutation11 permutation3
    _ = injectiveMoment H node177 := by rfl

def raw2834 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![2, -3, 1]]

theorem canonical2834 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2834 = injectiveMoment H node182 := by
  rfl

def raw2835 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 2, -3]]

theorem canonical2835 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2835 = injectiveMoment H node183 := by
  rfl

def raw2836 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]

def raw2836step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical2836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2836 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw2836 = injectiveMoment H raw2836step0 := by
      have hz : ∀ j, raw2836 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw2836step0 = (fun i j => raw2836 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2836 permutation104 hz
    _ = injectiveMoment H node184 := by rfl

def raw2837 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]

def raw2837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical2837 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2837 = injectiveMoment H node572 := by
  calc
    injectiveMoment H raw2837 = injectiveMoment H raw2837step0 := by
      have heq : raw2837step0 = (fun i j => raw2837 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2837 permutation45 permutation3
    _ = injectiveMoment H node572 := by rfl

def raw2838 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]

def raw2838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical2838 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2838 = injectiveMoment H node572 := by
  calc
    injectiveMoment H raw2838 = injectiveMoment H raw2838step0 := by
      have heq : raw2838step0 = (fun i j => raw2838 (permutation51 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2838 permutation51 permutation3
    _ = injectiveMoment H node572 := by rfl

def raw2839 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical2839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2839 = injectiveMoment H node184 := by
  rfl

def raw2840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]

def raw2840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2840 = injectiveMoment H node561 := by
  calc
    injectiveMoment H raw2840 = injectiveMoment H raw2840step0 := by
      have heq : raw2840step0 = (fun i j => raw2840 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2840 permutation45 permutation3
    _ = injectiveMoment H node561 := by rfl

def raw2841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]

def raw2841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical2841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2841 = injectiveMoment H node573 := by
  calc
    injectiveMoment H raw2841 = injectiveMoment H raw2841step0 := by
      have heq : raw2841step0 = (fun i j => raw2841 (permutation51 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2841 permutation51 permutation3
    _ = injectiveMoment H node573 := by rfl

def raw2842 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2842 = injectiveMoment H node185 := by
  rfl

def raw2843 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw2843step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2843 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw2843 = injectiveMoment H raw2843step0 := by
      have heq : raw2843step0 = (fun i j => raw2843 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2843 permutation10 permutation3
    _ = injectiveMoment H node185 := by rfl

def raw2844 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]

def raw2844step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical2844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2844 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw2844 = injectiveMoment H raw2844step0 := by
      have heq : raw2844step0 = (fun i j => raw2844 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2844 permutation10 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw2845 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

def raw2846 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

theorem canonical2846 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2846 = injectiveMoment H node186 := by
  rfl

def raw2847 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical2847 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2847 = injectiveMoment H node187 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
