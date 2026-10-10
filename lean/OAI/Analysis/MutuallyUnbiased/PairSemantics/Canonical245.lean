import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical7840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7840 = injectiveMoment H node1341 := by
  rfl

def raw7841 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, 2, -1], ![1, 0, -1, 0]]

def raw7841step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0]]

def raw7841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7841 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw7841 = injectiveMoment H raw7841step0 := by
      have heq : raw7841step0 = raw7841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7841).symm
    injectiveMoment H raw7841step0 = injectiveMoment H raw7841step1 := by
      have heq : raw7841step1 = (fun i j => raw7841step0 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7841step0 permutation24 permutation7
    _ = injectiveMoment H node287 := by rfl

def raw7842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem canonical7842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7842 = injectiveMoment H node1344 := by
  rfl

def raw7843 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

theorem canonical7843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7843 = injectiveMoment H node1345 := by
  rfl

def raw7844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7844step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -2, 0, 3], ![1, 2, -1, -2]]

def raw7844step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![1, 2, 0, -3], ![-1, -2, 1, 2]]

def raw7844step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical7844 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7844 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw7844 = injectiveMoment H raw7844step0 := by
      have heq : raw7844step0 = raw7844.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7844).symm
    injectiveMoment H raw7844step0 = injectiveMoment H raw7844step1 := by
      have heq : raw7844step1 = -raw7844step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7844step0).symm
    injectiveMoment H raw7844step1 = injectiveMoment H raw7844step2 := by
      have heq : raw7844step2 = (fun i j => raw7844step1 (permutation15 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7844step1 permutation15 permutation21
    _ = injectiveMoment H node1083 := by rfl

def raw7845 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical7845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7845 = injectiveMoment H node1346 := by
  rfl

def raw7846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical7846 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7846 = injectiveMoment H node1347 := by
  rfl

def raw7847 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical7847 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7847 = injectiveMoment H node1348 := by
  rfl

def raw7848 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![1, -1, 3, -3]]

def raw7848step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, -2, 3], ![1, 2, -3]]

def raw7848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical7848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7848 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw7848 = injectiveMoment H raw7848step0 := by
      have heq : raw7848step0 = raw7848.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7848).symm
    injectiveMoment H raw7848step0 = injectiveMoment H raw7848step1 := by
      have heq : raw7848step1 = (fun i j => raw7848step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7848step0 permutation21 permutation5
    _ = injectiveMoment H node168 := by rfl

def raw7849 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7849step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical7849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7849 = injectiveMoment H node2841 := by
  calc
    injectiveMoment H raw7849 = injectiveMoment H raw7849step0 := by
      have heq : raw7849step0 = (fun i j => raw7849 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7849 permutation39 permutation9
    _ = injectiveMoment H node2841 := by rfl

def raw7850 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

theorem canonical7850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7850 = injectiveMoment H node2842 := by
  rfl

def raw7851 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical7851 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7851 = injectiveMoment H node2843 := by
  rfl

def raw7852 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical7852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7852 = injectiveMoment H node2844 := by
  rfl

def raw7853 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical7853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7853 = injectiveMoment H node2845 := by
  rfl

def raw7854 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7854step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, -1, 2, 0], ![1, 1, -2, 0]]

def raw7854step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical7854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7854 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw7854 = injectiveMoment H raw7854step0 := by
      have heq : raw7854step0 = raw7854.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7854).symm
    injectiveMoment H raw7854step0 = injectiveMoment H raw7854step1 := by
      have heq : raw7854step1 = (fun i j => raw7854step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7854step0 permutation23 permutation19
    _ = injectiveMoment H node1241 := by rfl

def raw7855 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1]]

theorem canonical7855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7855 = injectiveMoment H node1350 := by
  rfl

def raw7856 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 3, -2]]

def raw7856step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, -1, 3], ![1, 1, 0, -2]]

def raw7856step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical7856 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7856 = injectiveMoment H node964 := by
  calc
    injectiveMoment H raw7856 = injectiveMoment H raw7856step0 := by
      have heq : raw7856step0 = raw7856.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7856).symm
    injectiveMoment H raw7856step0 = injectiveMoment H raw7856step1 := by
      have heq : raw7856step1 = (fun i j => raw7856step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7856step0 permutation21 permutation17
    _ = injectiveMoment H node964 := by rfl

def raw7857 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, 0, 2], ![1, 1, -1, -1]]

def raw7857step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical7857 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7857 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw7857 = injectiveMoment H raw7857step0 := by
      have heq : raw7857step0 = raw7857.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7857).symm
    injectiveMoment H raw7857step0 = injectiveMoment H raw7857step1 := by
      have heq : raw7857step1 = (fun i j => raw7857step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7857step0 permutation21 permutation17
    _ = injectiveMoment H node1260 := by rfl

def raw7858 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7858step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, 0, 1, -1], ![0, -1, -1, 2], ![-1, 2, -1, 0]]

def raw7858step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical7858 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7858 = injectiveMoment H node1006 := by
  calc
    injectiveMoment H raw7858 = injectiveMoment H raw7858step0 := by
      have heq : raw7858step0 = -raw7858 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7858).symm
    injectiveMoment H raw7858step0 = injectiveMoment H raw7858step1 := by
      have heq : raw7858step1 = (fun i j => raw7858step0 (permutation32 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7858step0 permutation32 permutation12
    _ = injectiveMoment H node1006 := by rfl

def raw7859 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw7859step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, 2, 0], ![1, 1, -3, 1]]

def raw7859step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![1, 1, -2, 0], ![-1, -1, 3, -1]]

def raw7859step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical7859 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7859 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw7859 = injectiveMoment H raw7859step0 := by
      have heq : raw7859step0 = raw7859.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7859).symm
    injectiveMoment H raw7859step0 = injectiveMoment H raw7859step1 := by
      have heq : raw7859step1 = -raw7859step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7859step0).symm
    injectiveMoment H raw7859step1 = injectiveMoment H raw7859step2 := by
      have heq : raw7859step2 = (fun i j => raw7859step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7859step1 permutation27 permutation19
    _ = injectiveMoment H node939 := by rfl

def raw7860 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw7860step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, 3, -1], ![1, 1, -4, 2]]

def raw7860step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![1, 1, -3, 1], ![-1, -1, 4, -2]]

def raw7860step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

theorem canonical7860 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7860 = injectiveMoment H node893 := by
  calc
    injectiveMoment H raw7860 = injectiveMoment H raw7860step0 := by
      have heq : raw7860step0 = raw7860.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7860).symm
    injectiveMoment H raw7860step0 = injectiveMoment H raw7860step1 := by
      have heq : raw7860step1 = -raw7860step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7860step0).symm
    injectiveMoment H raw7860step1 = injectiveMoment H raw7860step2 := by
      have heq : raw7860step2 = (fun i j => raw7860step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7860step1 permutation29 permutation16
    _ = injectiveMoment H node893 := by rfl

def raw7861 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7861step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 0, 1, 0], ![1, 0, -1, 0]]

def raw7861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw7861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7861 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw7861 = injectiveMoment H raw7861step0 := by
      have heq : raw7861step0 = raw7861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7861).symm
    injectiveMoment H raw7861step0 = injectiveMoment H raw7861step1 := by
      have hz : ∀ i, raw7861step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7861step1 = (fun i j => raw7861step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7861step0 permutation15 hz
    injectiveMoment H raw7861step1 = injectiveMoment H raw7861step2 := by
      have heq : raw7861step2 = (fun i j => raw7861step1 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7861step1 permutation29 permutation6
    _ = injectiveMoment H node293 := by rfl

def raw7862 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 0, 0], ![1, -1, 1, -1]]

def raw7862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1]]

def raw7862step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7862step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7862 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7862 = injectiveMoment H raw7862step0 := by
      have heq : raw7862step0 = raw7862.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7862).symm
    injectiveMoment H raw7862step0 = injectiveMoment H raw7862step1 := by
      have hz : ∀ i, raw7862step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7862step1 = (fun i j => raw7862step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7862step0 permutation5 hz
    injectiveMoment H raw7862step1 = injectiveMoment H raw7862step2 := by
      have heq : raw7862step2 = (fun i j => raw7862step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7862step1 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7863 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0]]

def raw7863step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![1, -1, 0, 0]]

def raw7863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw7863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7863 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw7863 = injectiveMoment H raw7863step0 := by
      have heq : raw7863step0 = raw7863.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7863).symm
    injectiveMoment H raw7863step0 = injectiveMoment H raw7863step1 := by
      have hz : ∀ i, raw7863step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw7863step1 = (fun i j => raw7863step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7863step0 permutation21 hz
    injectiveMoment H raw7863step1 = injectiveMoment H raw7863step2 := by
      have heq : raw7863step2 = (fun i j => raw7863step1 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7863step1 permutation29 permutation6
    _ = injectiveMoment H node293 := by rfl

def raw7864 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1]]

def raw7864step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw7864step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem canonical7864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7864 = injectiveMoment H node1114 := by
  calc
    injectiveMoment H raw7864 = injectiveMoment H raw7864step0 := by
      have heq : raw7864step0 = raw7864.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7864).symm
    injectiveMoment H raw7864step0 = injectiveMoment H raw7864step1 := by
      have heq : raw7864step1 = (fun i j => raw7864step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7864step0 permutation27 permutation17
    _ = injectiveMoment H node1114 := by rfl

def raw7865 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7865step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 1, 2, -2], ![1, -1, -3, 3]]

def raw7865step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical7865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7865 = injectiveMoment H node1326 := by
  calc
    injectiveMoment H raw7865 = injectiveMoment H raw7865step0 := by
      have heq : raw7865step0 = raw7865.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7865).symm
    injectiveMoment H raw7865step0 = injectiveMoment H raw7865step1 := by
      have heq : raw7865step1 = (fun i j => raw7865step0 (permutation27 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7865step0 permutation27 permutation15
    _ = injectiveMoment H node1326 := by rfl

def raw7866 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7866step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw7866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7866 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7866 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw7866 = injectiveMoment H raw7866step0 := by
      have heq : raw7866step0 = raw7866.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7866).symm
    injectiveMoment H raw7866step0 = injectiveMoment H raw7866step1 := by
      have heq : raw7866step1 = (fun i j => raw7866step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7866step0 permutation29 permutation6
    _ = injectiveMoment H node293 := by rfl

def raw7867 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7867step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 2, -1, 0], ![1, -2, 0, 1]]

def raw7867step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical7867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7867 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw7867 = injectiveMoment H raw7867step0 := by
      have heq : raw7867step0 = raw7867.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7867).symm
    injectiveMoment H raw7867step0 = injectiveMoment H raw7867step1 := by
      have heq : raw7867step1 = (fun i j => raw7867step0 (permutation22 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7867step0 permutation22 permutation22
    _ = injectiveMoment H node1000 := by rfl

def raw7868 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

theorem canonical7868 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7868 = injectiveMoment H node1351 := by
  rfl

def raw7869 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1]]

def raw7869step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1]]

def raw7869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical7869 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7869 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw7869 = injectiveMoment H raw7869step0 := by
      have heq : raw7869step0 = raw7869.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7869).symm
    injectiveMoment H raw7869step0 = injectiveMoment H raw7869step1 := by
      have heq : raw7869step1 = (fun i j => raw7869step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7869step0 permutation27 permutation5
    _ = injectiveMoment H node227 := by rfl

def raw7870 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

theorem canonical7870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7870 = injectiveMoment H node1352 := by
  rfl

def raw7871 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, -1, 2]]

def raw7871step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 3, -1, -1], ![1, -3, 0, 2]]

def raw7871step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical7871 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7871 = injectiveMoment H node937 := by
  calc
    injectiveMoment H raw7871 = injectiveMoment H raw7871step0 := by
      have heq : raw7871step0 = raw7871.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7871).symm
    injectiveMoment H raw7871step0 = injectiveMoment H raw7871step1 := by
      have heq : raw7871step1 = (fun i j => raw7871step0 (permutation22 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7871step0 permutation22 permutation22
    _ = injectiveMoment H node937 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
