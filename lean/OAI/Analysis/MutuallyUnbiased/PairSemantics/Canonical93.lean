import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2976 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

theorem canonical2976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2976 = injectiveMoment H node1931 := by
  rfl

def raw2977 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2977step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 1, -1, 2]]

def raw2977step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

theorem canonical2977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2977 = injectiveMoment H node1302 := by
  calc
    injectiveMoment H raw2977 = injectiveMoment H raw2977step0 := by
      have heq : raw2977step0 = -raw2977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2977).symm
    injectiveMoment H raw2977step0 = injectiveMoment H raw2977step1 := by
      have heq : raw2977step1 = (fun i j => raw2977step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2977step0 permutation23 permutation15
    _ = injectiveMoment H node1302 := by rfl

def raw2978 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2978step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2978step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2978 = injectiveMoment H node2739 := by
  calc
    injectiveMoment H raw2978 = injectiveMoment H raw2978step0 := by
      have heq : raw2978step0 = -raw2978 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2978).symm
    injectiveMoment H raw2978step0 = injectiveMoment H raw2978step1 := by
      have heq : raw2978step1 = (fun i j => raw2978step0 (permutation90 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2978step0 permutation90 permutation17
    _ = injectiveMoment H node2739 := by rfl

def raw2979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![4, -2, -1, -1]]

def raw2979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical2979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2979 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw2979 = injectiveMoment H raw2979step0 := by
      have heq : raw2979step0 = raw2979.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2979).symm
    injectiveMoment H raw2979step0 = injectiveMoment H raw2979step1 := by
      have heq : raw2979step1 = (fun i j => raw2979step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2979step0 permutation28 permutation24
    _ = injectiveMoment H node775 := by rfl

def raw2980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![0, -1, -1, 2], ![-2, 1, 1, 0]]

def raw2980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical2980 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2980 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw2980 = injectiveMoment H raw2980step0 := by
      have heq : raw2980step0 = -raw2980 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2980).symm
    injectiveMoment H raw2980step0 = injectiveMoment H raw2980step1 := by
      have heq : raw2980step1 = (fun i j => raw2980step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2980step0 permutation23 permutation15
    _ = injectiveMoment H node1257 := by rfl

def raw2981 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical2981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2981 = injectiveMoment H node1932 := by
  rfl

def raw2982 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw2982step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical2982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2982 = injectiveMoment H node1932 := by
  calc
    injectiveMoment H raw2982 = injectiveMoment H raw2982step0 := by
      have heq : raw2982step0 = (fun i j => raw2982 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2982 permutation34 permutation9
    _ = injectiveMoment H node1932 := by rfl

def raw2983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 1, -1]]

def raw2983step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![-2, 2, -1, 1], ![4, -2, -1, -1]]

def raw2983step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem canonical2983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2983 = injectiveMoment H node459 := by
  calc
    injectiveMoment H raw2983 = injectiveMoment H raw2983step0 := by
      have heq : raw2983step0 = raw2983.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2983).symm
    injectiveMoment H raw2983step0 = injectiveMoment H raw2983step1 := by
      have heq : raw2983step1 = (fun i j => raw2983step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2983step0 permutation27 permutation18
    _ = injectiveMoment H node459 := by rfl

def raw2984 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw2984step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical2984 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2984 = injectiveMoment H node1475 := by
  calc
    injectiveMoment H raw2984 = injectiveMoment H raw2984step0 := by
      have heq : raw2984step0 = (fun i j => raw2984 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2984 permutation42 permutation21
    _ = injectiveMoment H node1475 := by rfl

def raw2985 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -2, 0, 0]]

def raw2985step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical2985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2985 = injectiveMoment H node395 := by
  calc
    injectiveMoment H raw2985 = injectiveMoment H raw2985step0 := by
      have heq : raw2985step0 = (fun i j => raw2985 (permutation12 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2985 permutation12 permutation21
    _ = injectiveMoment H node395 := by rfl

def raw2986 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2986step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw2986step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical2986 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2986 = injectiveMoment H node1113 := by
  calc
    injectiveMoment H raw2986 = injectiveMoment H raw2986step0 := by
      have heq : raw2986step0 = -raw2986 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2986).symm
    injectiveMoment H raw2986step0 = injectiveMoment H raw2986step1 := by
      have heq : raw2986step1 = (fun i j => raw2986step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2986step0 permutation29 permutation15
    _ = injectiveMoment H node1113 := by rfl

def raw2987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, -1, 1, -1]]

def raw2987step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![-1, -1, 1, 1], ![-1, 1, -1, 1]]

def raw2987step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical2987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2987 = injectiveMoment H node1113 := by
  calc
    injectiveMoment H raw2987 = injectiveMoment H raw2987step0 := by
      have heq : raw2987step0 = -raw2987 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2987).symm
    injectiveMoment H raw2987step0 = injectiveMoment H raw2987step1 := by
      have heq : raw2987step1 = (fun i j => raw2987step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2987step0 permutation23 permutation15
    _ = injectiveMoment H node1113 := by rfl

def raw2988 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical2988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2988 = injectiveMoment H node1933 := by
  rfl

def raw2989 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -2, 0, 0]]

theorem canonical2989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2989 = injectiveMoment H node582 := by
  rfl

def raw2990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-2, 3, 0, -1], ![4, -3, 0, -1]]

def raw2990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![2, -3, 0, 1], ![-4, 3, 0, 1]]

def raw2990step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical2990 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2990 = injectiveMoment H node1075 := by
  calc
    injectiveMoment H raw2990 = injectiveMoment H raw2990step0 := by
      have heq : raw2990step0 = raw2990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2990).symm
    injectiveMoment H raw2990step0 = injectiveMoment H raw2990step1 := by
      have heq : raw2990step1 = -raw2990step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2990step0).symm
    injectiveMoment H raw2990step1 = injectiveMoment H raw2990step2 := by
      have heq : raw2990step2 = (fun i j => raw2990step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2990step1 permutation12 permutation26
    _ = injectiveMoment H node1075 := by rfl

def raw2991 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![1, 1, -1, -1], ![1, -1, 0, 0]]

def raw2991step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![-2, 3, -1, 0], ![4, -3, -1, 0]]

def raw2991step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![2, -3, 1, 0], ![-4, 3, 1, 0]]

def raw2991step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical2991 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2991 = injectiveMoment H node1075 := by
  calc
    injectiveMoment H raw2991 = injectiveMoment H raw2991step0 := by
      have heq : raw2991step0 = raw2991.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2991).symm
    injectiveMoment H raw2991step0 = injectiveMoment H raw2991step1 := by
      have heq : raw2991step1 = -raw2991step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2991step0).symm
    injectiveMoment H raw2991step1 = injectiveMoment H raw2991step2 := by
      have heq : raw2991step2 = (fun i j => raw2991step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2991step1 permutation12 permutation32
    _ = injectiveMoment H node1075 := by rfl

def raw2992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, -1, 1, -2]]

def raw2992step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, 1, 0], ![0, 0, -2, 2], ![-2, 1, -1, 2]]

def raw2992step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

theorem canonical2992 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2992 = injectiveMoment H node1302 := by
  calc
    injectiveMoment H raw2992 = injectiveMoment H raw2992step0 := by
      have heq : raw2992step0 = -raw2992 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2992).symm
    injectiveMoment H raw2992step0 = injectiveMoment H raw2992step1 := by
      have heq : raw2992step1 = (fun i j => raw2992step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2992step0 permutation17 permutation15
    _ = injectiveMoment H node1302 := by rfl

def raw2993 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical2993 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2993 = injectiveMoment H node1934 := by
  rfl

def raw2994 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical2994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2994 = injectiveMoment H node1935 := by
  rfl

def raw2995 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical2995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2995 = injectiveMoment H node1936 := by
  rfl

def raw2996 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw2996step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 0, 3], ![4, 0, -1, -3]]

def raw2996step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![2, 1, 0, -3], ![-4, 0, 1, 3]]

def raw2996step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -4, 3], ![1, 0, 2, -3]]

theorem canonical2996 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2996 = injectiveMoment H node1051 := by
  calc
    injectiveMoment H raw2996 = injectiveMoment H raw2996step0 := by
      have heq : raw2996step0 = raw2996.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2996).symm
    injectiveMoment H raw2996step0 = injectiveMoment H raw2996step1 := by
      have heq : raw2996step1 = -raw2996step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2996step0).symm
    injectiveMoment H raw2996step1 = injectiveMoment H raw2996step2 := by
      have heq : raw2996step2 = (fun i j => raw2996step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2996step1 permutation16 permutation17
    _ = injectiveMoment H node1051 := by rfl

def raw2997 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical2997 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2997 = injectiveMoment H node1937 := by
  rfl

def raw2998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw2998step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 1, 2], ![4, 0, -2, -2]]

def raw2998step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![2, 1, -1, -2], ![-4, 0, 2, 2]]

def raw2998step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -4, 2], ![1, -1, 2, -2]]

theorem canonical2998 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2998 = injectiveMoment H node1055 := by
  calc
    injectiveMoment H raw2998 = injectiveMoment H raw2998step0 := by
      have heq : raw2998step0 = raw2998.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2998).symm
    injectiveMoment H raw2998step0 = injectiveMoment H raw2998step1 := by
      have heq : raw2998step1 = -raw2998step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2998step0).symm
    injectiveMoment H raw2998step1 = injectiveMoment H raw2998step2 := by
      have heq : raw2998step2 = (fun i j => raw2998step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2998step1 permutation16 permutation17
    _ = injectiveMoment H node1055 := by rfl

def raw2999 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical2999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2999 = injectiveMoment H node1938 := by
  rfl

def raw3000 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3000step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical3000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3000 = injectiveMoment H node1938 := by
  calc
    injectiveMoment H raw3000 = injectiveMoment H raw3000step0 := by
      have heq : raw3000step0 = (fun i j => raw3000 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3000 permutation34 permutation9
    _ = injectiveMoment H node1938 := by rfl

def raw3001 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 1, -1]]

def raw3001step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 2, 1], ![4, 0, -3, -1]]

def raw3001step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![2, 1, -2, -1], ![-4, 0, 3, 1]]

def raw3001step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 3, 1, -4], ![1, -2, -1, 2]]

theorem canonical3001 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3001 = injectiveMoment H node1159 := by
  calc
    injectiveMoment H raw3001 = injectiveMoment H raw3001step0 := by
      have heq : raw3001step0 = raw3001.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3001).symm
    injectiveMoment H raw3001step0 = injectiveMoment H raw3001step1 := by
      have heq : raw3001step1 = -raw3001step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3001step0).symm
    injectiveMoment H raw3001step1 = injectiveMoment H raw3001step2 := by
      have heq : raw3001step2 = (fun i j => raw3001step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3001step1 permutation16 permutation18
    _ = injectiveMoment H node1159 := by rfl

def raw3002 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical3002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3002 = injectiveMoment H node1939 := by
  rfl

def raw3003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 3, 0], ![4, 0, -4, 0]]

def raw3003step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 2, -2, 0], ![1, -2, 0, 1]]

theorem canonical3003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3003 = injectiveMoment H node1229 := by
  calc
    injectiveMoment H raw3003 = injectiveMoment H raw3003step0 := by
      have heq : raw3003step0 = raw3003.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3003).symm
    injectiveMoment H raw3003step0 = injectiveMoment H raw3003step1 := by
      have heq : raw3003step1 = (fun i j => raw3003step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3003step0 permutation25 permutation19
    _ = injectiveMoment H node1229 := by rfl

def raw3004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, -1, 1, 2], ![4, 0, 0, -4]]

def raw3004step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -2, 0, 1]]

theorem canonical3004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3004 = injectiveMoment H node1338 := by
  calc
    injectiveMoment H raw3004 = injectiveMoment H raw3004step0 := by
      have heq : raw3004step0 = raw3004.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3004).symm
    injectiveMoment H raw3004step0 = injectiveMoment H raw3004step1 := by
      have heq : raw3004step1 = (fun i j => raw3004step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3004step0 permutation25 permutation17
    _ = injectiveMoment H node1338 := by rfl

def raw3005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3005step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![4, 0, 0, -4]]

def raw3005step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -1, 0, 0]]

theorem canonical3005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3005 = injectiveMoment H node1227 := by
  calc
    injectiveMoment H raw3005 = injectiveMoment H raw3005step0 := by
      have heq : raw3005step0 = raw3005.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3005).symm
    injectiveMoment H raw3005step0 = injectiveMoment H raw3005step1 := by
      have heq : raw3005step1 = (fun i j => raw3005step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3005step0 permutation25 permutation17
    _ = injectiveMoment H node1227 := by rfl

def raw3006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw3006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, -2, 3]]

def raw3006step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical3006 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3006 = injectiveMoment H node1298 := by
  calc
    injectiveMoment H raw3006 = injectiveMoment H raw3006step0 := by
      have heq : raw3006step0 = -raw3006 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3006).symm
    injectiveMoment H raw3006step0 = injectiveMoment H raw3006step1 := by
      have heq : raw3006step1 = (fun i j => raw3006step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3006step0 permutation19 permutation15
    _ = injectiveMoment H node1298 := by rfl

def raw3007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3007step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem canonical3007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3007 = injectiveMoment H node1458 := by
  calc
    injectiveMoment H raw3007 = injectiveMoment H raw3007step0 := by
      have heq : raw3007step0 = (fun i j => raw3007 (permutation33 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3007 permutation33 permutation21
    _ = injectiveMoment H node1458 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
