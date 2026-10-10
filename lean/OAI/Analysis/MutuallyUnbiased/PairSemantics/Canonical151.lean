import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4832 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4832step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -3, 3, 0], ![1, 2, -2, -1]]

def raw4832step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

theorem canonical4832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4832 = injectiveMoment H node1369 := by
  calc
    injectiveMoment H raw4832 = injectiveMoment H raw4832step0 := by
      have heq : raw4832step0 = raw4832.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4832).symm
    injectiveMoment H raw4832step0 = injectiveMoment H raw4832step1 := by
      have heq : raw4832step1 = (fun i j => raw4832step0 (permutation32 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4832step0 permutation32 permutation27
    _ = injectiveMoment H node1369 := by rfl

def raw4833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4833step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -3, 0, 3], ![1, 2, 0, -3]]

def raw4833step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 0, 1]]

theorem canonical4833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4833 = injectiveMoment H node1365 := by
  calc
    injectiveMoment H raw4833 = injectiveMoment H raw4833step0 := by
      have heq : raw4833step0 = raw4833.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4833).symm
    injectiveMoment H raw4833step0 = injectiveMoment H raw4833step1 := by
      have heq : raw4833step1 = (fun i j => raw4833step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4833step0 permutation18 permutation21
    _ = injectiveMoment H node1365 := by rfl

def raw4834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw4834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -2, -1, 3], ![1, 1, 2, -4]]

def raw4834step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

theorem canonical4834 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4834 = injectiveMoment H node586 := by
  calc
    injectiveMoment H raw4834 = injectiveMoment H raw4834step0 := by
      have heq : raw4834step0 = raw4834.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4834).symm
    injectiveMoment H raw4834step0 = injectiveMoment H raw4834step1 := by
      have heq : raw4834step1 = (fun i j => raw4834step0 (permutation21 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4834step0 permutation21 permutation15
    _ = injectiveMoment H node586 := by rfl

def raw4835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw4835step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, 2, -1], ![-1, 2, 0, -1], ![-1, 0, -2, 3]]

def raw4835step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical4835 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4835 = injectiveMoment H node473 := by
  calc
    injectiveMoment H raw4835 = injectiveMoment H raw4835step0 := by
      have heq : raw4835step0 = -raw4835 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4835).symm
    injectiveMoment H raw4835step0 = injectiveMoment H raw4835step1 := by
      have heq : raw4835step1 = (fun i j => raw4835step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4835step0 permutation31 permutation21
    _ = injectiveMoment H node473 := by rfl

def raw4836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -2, 3, -1], ![1, 1, -2, 0]]

def raw4836step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

theorem canonical4836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4836 = injectiveMoment H node820 := by
  calc
    injectiveMoment H raw4836 = injectiveMoment H raw4836step0 := by
      have heq : raw4836step0 = raw4836.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4836).symm
    injectiveMoment H raw4836step0 = injectiveMoment H raw4836step1 := by
      have heq : raw4836step1 = (fun i j => raw4836step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4836step0 permutation24 permutation29
    _ = injectiveMoment H node820 := by rfl

def raw4837 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4837step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -2, -1, 3], ![1, 1, 1, -3]]

def raw4837step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical4837 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4837 = injectiveMoment H node487 := by
  calc
    injectiveMoment H raw4837 = injectiveMoment H raw4837step0 := by
      have heq : raw4837step0 = raw4837.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4837).symm
    injectiveMoment H raw4837step0 = injectiveMoment H raw4837step1 := by
      have heq : raw4837step1 = (fun i j => raw4837step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4837step0 permutation21 permutation17
    _ = injectiveMoment H node487 := by rfl

def raw4838 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4838step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -2, 0, 2], ![1, 1, 0, -2]]

def raw4838step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![0, 2, 0, -2], ![-1, -1, 0, 2]]

def raw4838step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical4838 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4838 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw4838 = injectiveMoment H raw4838step0 := by
      have heq : raw4838step0 = raw4838.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4838).symm
    injectiveMoment H raw4838step0 = injectiveMoment H raw4838step1 := by
      have heq : raw4838step1 = -raw4838step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4838step0).symm
    injectiveMoment H raw4838step1 = injectiveMoment H raw4838step2 := by
      have heq : raw4838step2 = (fun i j => raw4838step1 (permutation14 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4838step1 permutation14 permutation23
    _ = injectiveMoment H node1309 := by rfl

def raw4839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical4839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4839 = injectiveMoment H node614 := by
  calc
    injectiveMoment H raw4839 = injectiveMoment H raw4839step0 := by
      have heq : raw4839step0 = (fun i j => raw4839 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4839 permutation9 permutation11
    _ = injectiveMoment H node614 := by rfl

def raw4840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 3, -3]]

def raw4840step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -1, -2, 3], ![1, 0, 2, -3]]

def raw4840step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![0, 1, 2, -3], ![-1, 0, -2, 3]]

def raw4840step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical4840 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4840 = injectiveMoment H node1093 := by
  calc
    injectiveMoment H raw4840 = injectiveMoment H raw4840step0 := by
      have heq : raw4840step0 = raw4840.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4840).symm
    injectiveMoment H raw4840step0 = injectiveMoment H raw4840step1 := by
      have heq : raw4840step1 = -raw4840step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4840step0).symm
    injectiveMoment H raw4840step1 = injectiveMoment H raw4840step2 := by
      have heq : raw4840step2 = (fun i j => raw4840step1 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4840step1 permutation19 permutation15
    _ = injectiveMoment H node1093 := by rfl

def raw4841 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw4841step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -1, -1, 2], ![1, 0, 1, -2]]

def raw4841step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical4841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4841 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw4841 = injectiveMoment H raw4841step0 := by
      have heq : raw4841step0 = raw4841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4841).symm
    injectiveMoment H raw4841step0 = injectiveMoment H raw4841step1 := by
      have heq : raw4841step1 = (fun i j => raw4841step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4841step0 permutation22 permutation17
    _ = injectiveMoment H node1078 := by rfl

def raw4842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw4842step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, 0, -2, 2], ![1, -1, 2, -2]]

def raw4842step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![0, 0, 2, -2], ![-1, 1, -2, 2]]

def raw4842step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical4842 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4842 = injectiveMoment H node1111 := by
  calc
    injectiveMoment H raw4842 = injectiveMoment H raw4842step0 := by
      have heq : raw4842step0 = raw4842.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4842).symm
    injectiveMoment H raw4842step0 = injectiveMoment H raw4842step1 := by
      have heq : raw4842step1 = -raw4842step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4842step0).symm
    injectiveMoment H raw4842step1 = injectiveMoment H raw4842step2 := by
      have heq : raw4842step2 = (fun i j => raw4842step1 (permutation17 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4842step1 permutation17 permutation16
    _ = injectiveMoment H node1111 := by rfl

def raw4843 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4843step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 1, -1, 1]]

def raw4843step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical4843 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4843 = injectiveMoment H node1119 := by
  calc
    injectiveMoment H raw4843 = injectiveMoment H raw4843step0 := by
      have heq : raw4843step0 = -raw4843 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4843).symm
    injectiveMoment H raw4843step0 = injectiveMoment H raw4843step1 := by
      have heq : raw4843step1 = (fun i j => raw4843step0 (permutation29 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4843step0 permutation29 permutation21
    _ = injectiveMoment H node1119 := by rfl

def raw4844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4844step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

theorem canonical4844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4844 = injectiveMoment H node620 := by
  calc
    injectiveMoment H raw4844 = injectiveMoment H raw4844step0 := by
      have heq : raw4844step0 = (fun i j => raw4844 (permutation10 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4844 permutation10 permutation12
    _ = injectiveMoment H node620 := by rfl

def raw4845 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw4845step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical4845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4845 = injectiveMoment H node513 := by
  calc
    injectiveMoment H raw4845 = injectiveMoment H raw4845step0 := by
      have heq : raw4845step0 = (fun i j => raw4845 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4845 permutation22 permutation23
    _ = injectiveMoment H node513 := by rfl

def raw4846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 2, -3], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4846step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, 2, -2, 0], ![1, -3, 2, 0]]

def raw4846step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical4846 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4846 = injectiveMoment H node1347 := by
  calc
    injectiveMoment H raw4846 = injectiveMoment H raw4846step0 := by
      have heq : raw4846step0 = raw4846.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4846).symm
    injectiveMoment H raw4846step0 = injectiveMoment H raw4846step1 := by
      have heq : raw4846step1 = (fun i j => raw4846step0 (permutation18 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4846step0 permutation18 permutation28
    _ = injectiveMoment H node1347 := by rfl

def raw4847 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw4847step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 1, -1]]

def raw4847step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical4847 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4847 = injectiveMoment H node477 := by
  calc
    injectiveMoment H raw4847 = injectiveMoment H raw4847step0 := by
      have heq : raw4847step0 = -raw4847 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4847).symm
    injectiveMoment H raw4847step0 = injectiveMoment H raw4847step1 := by
      have heq : raw4847step1 = (fun i j => raw4847step0 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4847step0 permutation15 permutation23
    _ = injectiveMoment H node477 := by rfl

def raw4848 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -3, 3], ![1, -1, 0, 0]]

def raw4848step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, 3, -3, 0], ![1, -4, 3, 0]]

def raw4848step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 1, 0]]

theorem canonical4848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4848 = injectiveMoment H node1343 := by
  calc
    injectiveMoment H raw4848 = injectiveMoment H raw4848step0 := by
      have heq : raw4848step0 = raw4848.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4848).symm
    injectiveMoment H raw4848step0 = injectiveMoment H raw4848step1 := by
      have heq : raw4848step1 = (fun i j => raw4848step0 (permutation18 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4848step0 permutation18 permutation28
    _ = injectiveMoment H node1343 := by rfl

def raw4849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

theorem canonical4849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4849 = injectiveMoment H node693 := by
  rfl

def raw4850 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -2, 2]]

def raw4850step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

theorem canonical4850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4850 = injectiveMoment H node693 := by
  calc
    injectiveMoment H raw4850 = injectiveMoment H raw4850step0 := by
      have heq : raw4850step0 = (fun i j => raw4850 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4850 permutation10 permutation9
    _ = injectiveMoment H node693 := by rfl

def raw4851 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, -2, 3], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw4851step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, -2, 3, -1], ![1, 3, -4, 0]]

def raw4851step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 1, 0]]

theorem canonical4851 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4851 = injectiveMoment H node1230 := by
  calc
    injectiveMoment H raw4851 = injectiveMoment H raw4851step0 := by
      have heq : raw4851step0 = raw4851.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4851).symm
    injectiveMoment H raw4851step0 = injectiveMoment H raw4851step1 := by
      have heq : raw4851step1 = (fun i j => raw4851step0 (permutation24 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4851step0 permutation24 permutation27
    _ = injectiveMoment H node1230 := by rfl

def raw4852 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, -1, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw4852step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, -1, -2, 3], ![1, 2, 1, -4]]

def raw4852step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

theorem canonical4852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4852 = injectiveMoment H node586 := by
  calc
    injectiveMoment H raw4852 = injectiveMoment H raw4852step0 := by
      have heq : raw4852step0 = raw4852.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4852).symm
    injectiveMoment H raw4852step0 = injectiveMoment H raw4852step1 := by
      have heq : raw4852step1 = (fun i j => raw4852step0 (permutation21 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4852step0 permutation21 permutation21
    _ = injectiveMoment H node586 := by rfl

def raw4853 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, -1, 2], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw4853step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, -1, 3, -2], ![1, 2, -4, 1]]

def raw4853step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical4853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4853 = injectiveMoment H node596 := by
  calc
    injectiveMoment H raw4853 = injectiveMoment H raw4853step0 := by
      have heq : raw4853step0 = raw4853.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4853).symm
    injectiveMoment H raw4853step0 = injectiveMoment H raw4853step1 := by
      have heq : raw4853step1 = (fun i j => raw4853step0 (permutation23 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4853step0 permutation23 permutation27
    _ = injectiveMoment H node596 := by rfl

def raw4854 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 3, -2], ![0, 0, -2, 2], ![1, 1, -1, -1]]

def raw4854step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![0, 3, -2, -1], ![1, -2, 2, -1]]

def raw4854step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem canonical4854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4854 = injectiveMoment H node484 := by
  calc
    injectiveMoment H raw4854 = injectiveMoment H raw4854step0 := by
      have heq : raw4854step0 = raw4854.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4854).symm
    injectiveMoment H raw4854step0 = injectiveMoment H raw4854step1 := by
      have heq : raw4854step1 = (fun i j => raw4854step0 (permutation21 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4854step0 permutation21 permutation25
    _ = injectiveMoment H node484 := by rfl

def raw4855 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 3, -2], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw4855step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, 3, -3, 0], ![1, -2, 2, -1]]

def raw4855step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

theorem canonical4855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4855 = injectiveMoment H node1369 := by
  calc
    injectiveMoment H raw4855 = injectiveMoment H raw4855step0 := by
      have heq : raw4855step0 = raw4855.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4855).symm
    injectiveMoment H raw4855step0 = injectiveMoment H raw4855step1 := by
      have heq : raw4855step1 = (fun i j => raw4855step0 (permutation32 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4855step0 permutation32 permutation28
    _ = injectiveMoment H node1369 := by rfl

def raw4856 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw4856step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![0, -3, 3, 0], ![1, 3, -4, 0]]

def raw4856step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 1, 0]]

theorem canonical4856 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4856 = injectiveMoment H node1343 := by
  calc
    injectiveMoment H raw4856 = injectiveMoment H raw4856step0 := by
      have heq : raw4856step0 = raw4856.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4856).symm
    injectiveMoment H raw4856step0 = injectiveMoment H raw4856step1 := by
      have heq : raw4856step1 = (fun i j => raw4856step0 (permutation18 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4856step0 permutation18 permutation27
    _ = injectiveMoment H node1343 := by rfl

def raw4857 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw4857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

theorem canonical4857 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4857 = injectiveMoment H node693 := by
  calc
    injectiveMoment H raw4857 = injectiveMoment H raw4857step0 := by
      have heq : raw4857step0 = (fun i j => raw4857 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4857 permutation11 permutation9
    _ = injectiveMoment H node693 := by rfl

def raw4858 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 3, -3], ![0, 1, -2, 1], ![1, -1, -1, 1]]

def raw4858step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![0, 3, -2, -1], ![1, -3, 1, 1]]

def raw4858step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical4858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4858 = injectiveMoment H node487 := by
  calc
    injectiveMoment H raw4858 = injectiveMoment H raw4858step0 := by
      have heq : raw4858step0 = raw4858.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4858).symm
    injectiveMoment H raw4858step0 = injectiveMoment H raw4858step1 := by
      have heq : raw4858step1 = (fun i j => raw4858step0 (permutation21 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4858step0 permutation21 permutation25
    _ = injectiveMoment H node487 := by rfl

def raw4859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw4859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical4859 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4859 = injectiveMoment H node2651 := by
  calc
    injectiveMoment H raw4859 = injectiveMoment H raw4859step0 := by
      have heq : raw4859step0 = -raw4859 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4859).symm
    injectiveMoment H raw4859step0 = injectiveMoment H raw4859step1 := by
      have heq : raw4859step1 = (fun i j => raw4859step0 (permutation164 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4859step0 permutation164 permutation6
    _ = injectiveMoment H node2651 := by rfl

def raw4860 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw4860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw4860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4860 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4860 = injectiveMoment H node1130 := by
  calc
    injectiveMoment H raw4860 = injectiveMoment H raw4860step0 := by
      have heq : raw4860step0 = -raw4860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4860).symm
    injectiveMoment H raw4860step0 = injectiveMoment H raw4860step1 := by
      have heq : raw4860step1 = (fun i j => raw4860step0 (permutation35 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4860step0 permutation35 permutation6
    _ = injectiveMoment H node1130 := by rfl

def raw4861 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]

def raw4861step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical4861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4861 = injectiveMoment H node275 := by
  calc
    injectiveMoment H raw4861 = injectiveMoment H raw4861step0 := by
      have heq : raw4861step0 = (fun i j => raw4861 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4861 permutation25 permutation6
    _ = injectiveMoment H node275 := by rfl

def raw4862 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4862 = injectiveMoment H node694 := by
  rfl

def raw4863 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]

def raw4863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 2, -3], ![-1, 1, 0], ![-2, -2, 4]]

def raw4863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

theorem canonical4863 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4863 = injectiveMoment H node132 := by
  calc
    injectiveMoment H raw4863 = injectiveMoment H raw4863step0 := by
      have heq : raw4863step0 = -raw4863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4863).symm
    injectiveMoment H raw4863step0 = injectiveMoment H raw4863step1 := by
      have heq : raw4863step1 = (fun i j => raw4863step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4863step0 permutation32 permutation3
    _ = injectiveMoment H node132 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
