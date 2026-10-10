import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9824 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9824step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical9824 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9824 = injectiveMoment H node2874 := by
  calc
    injectiveMoment H raw9824 = injectiveMoment H raw9824step0 := by
      have heq : raw9824step0 = (fun i j => raw9824 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9824 permutation308 permutation9
    _ = injectiveMoment H node2874 := by rfl

def raw9825 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -2, -2, 3]]

def raw9825step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical9825 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9825 = injectiveMoment H node2823 := by
  calc
    injectiveMoment H raw9825 = injectiveMoment H raw9825step0 := by
      have heq : raw9825step0 = (fun i j => raw9825 (permutation116 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9825 permutation116 permutation11
    _ = injectiveMoment H node2823 := by rfl

def raw9826 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9826step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9826 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9826 = injectiveMoment H node3098 := by
  calc
    injectiveMoment H raw9826 = injectiveMoment H raw9826step0 := by
      have heq : raw9826step0 = (fun i j => raw9826 (permutation396 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9826 permutation396 permutation17
    _ = injectiveMoment H node3098 := by rfl

def raw9827 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9827step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9827 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9827 = injectiveMoment H node2966 := by
  calc
    injectiveMoment H raw9827 = injectiveMoment H raw9827step0 := by
      have heq : raw9827step0 = (fun i j => raw9827 (permutation383 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9827 permutation383 permutation11
    _ = injectiveMoment H node2966 := by rfl

def raw9828 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9828step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9828 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9828 = injectiveMoment H node2997 := by
  calc
    injectiveMoment H raw9828 = injectiveMoment H raw9828step0 := by
      have heq : raw9828step0 = (fun i j => raw9828 (permutation310 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9828 permutation310 permutation9
    _ = injectiveMoment H node2997 := by rfl

def raw9829 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9829step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9829 = injectiveMoment H node2873 := by
  calc
    injectiveMoment H raw9829 = injectiveMoment H raw9829step0 := by
      have heq : raw9829step0 = (fun i j => raw9829 (permutation310 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9829 permutation310 permutation9
    _ = injectiveMoment H node2873 := by rfl

def raw9830 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, -1, 1]]

def raw9830step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem canonical9830 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9830 = injectiveMoment H node3000 := by
  calc
    injectiveMoment H raw9830 = injectiveMoment H raw9830step0 := by
      have heq : raw9830step0 = (fun i j => raw9830 (permutation286 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9830 permutation286 permutation11
    _ = injectiveMoment H node3000 := by rfl

def raw9831 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -2, 2]]

def raw9831step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9831 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9831 = injectiveMoment H node2891 := by
  calc
    injectiveMoment H raw9831 = injectiveMoment H raw9831step0 := by
      have heq : raw9831step0 = (fun i j => raw9831 (permutation395 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9831 permutation395 permutation17
    _ = injectiveMoment H node2891 := by rfl

def raw9832 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -2, 4]]

def raw9832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw9832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical9832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9832 = injectiveMoment H node441 := by
  calc
    injectiveMoment H raw9832 = injectiveMoment H raw9832step0 := by
      have hz : ∀ i, raw9832 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9832step0 = (fun i j => raw9832 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9832 permutation9 hz
    injectiveMoment H raw9832step0 = injectiveMoment H raw9832step1 := by
      have heq : raw9832step1 = (fun i j => raw9832step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9832step0 permutation128 permutation3
    _ = injectiveMoment H node441 := by rfl

def raw9833 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 0, -1, 3]]

def raw9833step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem canonical9833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9833 = injectiveMoment H node3000 := by
  calc
    injectiveMoment H raw9833 = injectiveMoment H raw9833step0 := by
      have heq : raw9833step0 = (fun i j => raw9833 (permutation363 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9833 permutation363 permutation11
    _ = injectiveMoment H node3000 := by rfl

def raw9834 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw9834step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9834 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9834 = injectiveMoment H node2876 := by
  calc
    injectiveMoment H raw9834 = injectiveMoment H raw9834step0 := by
      have heq : raw9834step0 = (fun i j => raw9834 (permutation363 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9834 permutation363 permutation11
    _ = injectiveMoment H node2876 := by rfl

def raw9835 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1], ![-2, -1, 0, 3]]

def raw9835step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem canonical9835 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9835 = injectiveMoment H node3000 := by
  calc
    injectiveMoment H raw9835 = injectiveMoment H raw9835step0 := by
      have heq : raw9835step0 = (fun i j => raw9835 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9835 permutation308 permutation9
    _ = injectiveMoment H node3000 := by rfl

def raw9836 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, -1, 4]]

def raw9836step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9836 = injectiveMoment H node2926 := by
  calc
    injectiveMoment H raw9836 = injectiveMoment H raw9836step0 := by
      have heq : raw9836step0 = (fun i j => raw9836 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9836 permutation308 permutation9
    _ = injectiveMoment H node2926 := by rfl

def raw9837 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0], ![-2, -2, 0, 4]]

def raw9837step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9837 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9837 = injectiveMoment H node2876 := by
  calc
    injectiveMoment H raw9837 = injectiveMoment H raw9837step0 := by
      have heq : raw9837step0 = (fun i j => raw9837 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9837 permutation308 permutation9
    _ = injectiveMoment H node2876 := by rfl

def raw9838 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, -1, 5]]

def raw9838step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9838 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9838 = injectiveMoment H node2865 := by
  calc
    injectiveMoment H raw9838 = injectiveMoment H raw9838step0 := by
      have heq : raw9838step0 = (fun i j => raw9838 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9838 permutation308 permutation9
    _ = injectiveMoment H node2865 := by rfl

def raw9839 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9839step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9839 = injectiveMoment H node3085 := by
  calc
    injectiveMoment H raw9839 = injectiveMoment H raw9839step0 := by
      have heq : raw9839step0 = (fun i j => raw9839 (permutation355 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9839 permutation355 permutation11
    _ = injectiveMoment H node3085 := by rfl

def raw9840 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9840step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical9840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9840 = injectiveMoment H node2927 := by
  calc
    injectiveMoment H raw9840 = injectiveMoment H raw9840step0 := by
      have heq : raw9840step0 = (fun i j => raw9840 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9840 permutation308 permutation9
    _ = injectiveMoment H node2927 := by rfl

def raw9841 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, -1, 2]]

def raw9841step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9841 = injectiveMoment H node3085 := by
  calc
    injectiveMoment H raw9841 = injectiveMoment H raw9841step0 := by
      have heq : raw9841step0 = (fun i j => raw9841 (permutation356 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9841 permutation356 permutation11
    _ = injectiveMoment H node3085 := by rfl

def raw9842 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -2, 3]]

def raw9842step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9842 = injectiveMoment H node2888 := by
  calc
    injectiveMoment H raw9842 = injectiveMoment H raw9842step0 := by
      have heq : raw9842step0 = (fun i j => raw9842 (permutation366 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9842 permutation366 permutation21
    _ = injectiveMoment H node2888 := by rfl

def raw9843 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1], ![-2, -1, -1, 4]]

def raw9843step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9843 = injectiveMoment H node2928 := by
  calc
    injectiveMoment H raw9843 = injectiveMoment H raw9843step0 := by
      have heq : raw9843step0 = (fun i j => raw9843 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9843 permutation308 permutation9
    _ = injectiveMoment H node2928 := by rfl

def raw9844 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -2, 5]]

def raw9844step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9844 = injectiveMoment H node2867 := by
  calc
    injectiveMoment H raw9844 = injectiveMoment H raw9844step0 := by
      have heq : raw9844step0 = (fun i j => raw9844 (permutation366 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9844 permutation366 permutation21
    _ = injectiveMoment H node2867 := by rfl

def raw9845 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9845step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical9845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9845 = injectiveMoment H node2871 := by
  calc
    injectiveMoment H raw9845 = injectiveMoment H raw9845step0 := by
      have heq : raw9845step0 = (fun i j => raw9845 (permutation310 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9845 permutation310 permutation15
    _ = injectiveMoment H node2871 := by rfl

def raw9846 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1], ![-2, -2, 0, 4]]

def raw9846step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9846 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9846 = injectiveMoment H node2875 := by
  calc
    injectiveMoment H raw9846 = injectiveMoment H raw9846step0 := by
      have heq : raw9846step0 = (fun i j => raw9846 (permutation310 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9846 permutation310 permutation15
    _ = injectiveMoment H node2875 := by rfl

def raw9847 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, -1, 5]]

def raw9847step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical9847 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9847 = injectiveMoment H node2864 := by
  calc
    injectiveMoment H raw9847 = injectiveMoment H raw9847step0 := by
      have heq : raw9847step0 = (fun i j => raw9847 (permutation310 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9847 permutation310 permutation15
    _ = injectiveMoment H node2864 := by rfl

def raw9848 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -2, -2, 4]]

def raw9848step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw9848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical9848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9848 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw9848 = injectiveMoment H raw9848step0 := by
      have hz : ∀ i, raw9848 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9848step0 = (fun i j => raw9848 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9848 permutation9 hz
    injectiveMoment H raw9848step0 = injectiveMoment H raw9848step1 := by
      have heq : raw9848step1 = (fun i j => raw9848step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9848step0 permutation27 permutation3
    _ = injectiveMoment H node145 := by rfl

def raw9849 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9849step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9849step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical9849 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9849 = injectiveMoment H node3246 := by
  calc
    injectiveMoment H raw9849 = injectiveMoment H raw9849step0 := by
      have heq : raw9849step0 = -raw9849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9849).symm
    injectiveMoment H raw9849step0 = injectiveMoment H raw9849step1 := by
      have heq : raw9849step1 = (fun i j => raw9849step0 (permutation373 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9849step0 permutation373 permutation15
    _ = injectiveMoment H node3246 := by rfl

def raw9850 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9850step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9850 = injectiveMoment H node3005 := by
  calc
    injectiveMoment H raw9850 = injectiveMoment H raw9850step0 := by
      have heq : raw9850step0 = (fun i j => raw9850 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9850 permutation312 permutation9
    _ = injectiveMoment H node3005 := by rfl

def raw9851 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9851step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw9851step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical9851 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9851 = injectiveMoment H node3196 := by
  calc
    injectiveMoment H raw9851 = injectiveMoment H raw9851step0 := by
      have heq : raw9851step0 = -raw9851 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9851).symm
    injectiveMoment H raw9851step0 = injectiveMoment H raw9851step1 := by
      have heq : raw9851step1 = (fun i j => raw9851step0 (permutation260 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9851step0 permutation260 permutation17
    _ = injectiveMoment H node3196 := by rfl

def raw9852 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9852step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9852 = injectiveMoment H node3003 := by
  calc
    injectiveMoment H raw9852 = injectiveMoment H raw9852step0 := by
      have heq : raw9852step0 = (fun i j => raw9852 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9852 permutation312 permutation9
    _ = injectiveMoment H node3003 := by rfl

def raw9853 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9853step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9853 = injectiveMoment H node2934 := by
  calc
    injectiveMoment H raw9853 = injectiveMoment H raw9853step0 := by
      have heq : raw9853step0 = (fun i j => raw9853 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9853 permutation312 permutation9
    _ = injectiveMoment H node2934 := by rfl

def raw9854 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9854step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9854step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical9854 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9854 = injectiveMoment H node3249 := by
  calc
    injectiveMoment H raw9854 = injectiveMoment H raw9854step0 := by
      have heq : raw9854step0 = -raw9854 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9854).symm
    injectiveMoment H raw9854step0 = injectiveMoment H raw9854step1 := by
      have heq : raw9854step1 = (fun i j => raw9854step0 (permutation373 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9854step0 permutation373 permutation15
    _ = injectiveMoment H node3249 := by rfl

def raw9855 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9855step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical9855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9855 = injectiveMoment H node3006 := by
  calc
    injectiveMoment H raw9855 = injectiveMoment H raw9855step0 := by
      have heq : raw9855step0 = (fun i j => raw9855 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9855 permutation312 permutation9
    _ = injectiveMoment H node3006 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
