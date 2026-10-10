import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8832 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8832step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8832step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

theorem canonical8832 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8832 = injectiveMoment H node3119 := by
  calc
    injectiveMoment H raw8832 = injectiveMoment H raw8832step0 := by
      have heq : raw8832step0 = -raw8832 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8832).symm
    injectiveMoment H raw8832step0 = injectiveMoment H raw8832step1 := by
      have heq : raw8832step1 = (fun i j => raw8832step0 (permutation343 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8832step0 permutation343 permutation9
    _ = injectiveMoment H node3119 := by rfl

def raw8833 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8833step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8833step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical8833 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8833 = injectiveMoment H node2909 := by
  calc
    injectiveMoment H raw8833 = injectiveMoment H raw8833step0 := by
      have heq : raw8833step0 = -raw8833 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8833).symm
    injectiveMoment H raw8833step0 = injectiveMoment H raw8833step1 := by
      have heq : raw8833step1 = (fun i j => raw8833step0 (permutation377 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8833step0 permutation377 permutation9
    _ = injectiveMoment H node2909 := by rfl

def raw8834 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8834step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 0, -2, 4]]

def raw8834step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical8834 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8834 = injectiveMoment H node3110 := by
  calc
    injectiveMoment H raw8834 = injectiveMoment H raw8834step0 := by
      have heq : raw8834step0 = -raw8834 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8834).symm
    injectiveMoment H raw8834step0 = injectiveMoment H raw8834step1 := by
      have heq : raw8834step1 = (fun i j => raw8834step0 (permutation377 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8834step0 permutation377 permutation9
    _ = injectiveMoment H node3110 := by rfl

def raw8835 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8835step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8835step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical8835 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8835 = injectiveMoment H node2917 := by
  calc
    injectiveMoment H raw8835 = injectiveMoment H raw8835step0 := by
      have heq : raw8835step0 = -raw8835 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8835).symm
    injectiveMoment H raw8835step0 = injectiveMoment H raw8835step1 := by
      have heq : raw8835step1 = (fun i j => raw8835step0 (permutation381 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8835step0 permutation381 permutation15
    _ = injectiveMoment H node2917 := by rfl

def raw8836 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8836step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8836 = injectiveMoment H node3271 := by
  calc
    injectiveMoment H raw8836 = injectiveMoment H raw8836step0 := by
      have heq : raw8836step0 = (fun i j => raw8836 (permutation283 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8836 permutation283 permutation9
    _ = injectiveMoment H node3271 := by rfl

def raw8837 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8837step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8837step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

theorem canonical8837 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8837 = injectiveMoment H node3119 := by
  calc
    injectiveMoment H raw8837 = injectiveMoment H raw8837step0 := by
      have heq : raw8837step0 = -raw8837 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8837).symm
    injectiveMoment H raw8837step0 = injectiveMoment H raw8837step1 := by
      have heq : raw8837step1 = (fun i j => raw8837step0 (permutation337 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8837step0 permutation337 permutation9
    _ = injectiveMoment H node3119 := by rfl

def raw8838 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8838step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8838step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical8838 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8838 = injectiveMoment H node3333 := by
  calc
    injectiveMoment H raw8838 = injectiveMoment H raw8838step0 := by
      have heq : raw8838step0 = -raw8838 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8838).symm
    injectiveMoment H raw8838step0 = injectiveMoment H raw8838step1 := by
      have heq : raw8838step1 = (fun i j => raw8838step0 (permutation340 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8838step0 permutation340 permutation15
    _ = injectiveMoment H node3333 := by rfl

def raw8839 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8839step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem canonical8839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8839 = injectiveMoment H node3459 := by
  calc
    injectiveMoment H raw8839 = injectiveMoment H raw8839step0 := by
      have heq : raw8839step0 = (fun i j => raw8839 (permutation152 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8839 permutation152 permutation15
    _ = injectiveMoment H node3459 := by rfl

def raw8840 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, -1, 2, -3]]

def raw8840step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw8840step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem canonical8840 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8840 = injectiveMoment H node3240 := by
  calc
    injectiveMoment H raw8840 = injectiveMoment H raw8840step0 := by
      have heq : raw8840step0 = -raw8840 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8840).symm
    injectiveMoment H raw8840step0 = injectiveMoment H raw8840step1 := by
      have heq : raw8840step1 = (fun i j => raw8840step0 (permutation339 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8840step0 permutation339 permutation9
    _ = injectiveMoment H node3240 := by rfl

def raw8841 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, -1, 1, 2], ![2, 1, 1, -4]]

def raw8841step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 1, -1, -2], ![-2, -1, -1, 4]]

def raw8841step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem canonical8841 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8841 = injectiveMoment H node2900 := by
  calc
    injectiveMoment H raw8841 = injectiveMoment H raw8841step0 := by
      have heq : raw8841step0 = -raw8841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8841).symm
    injectiveMoment H raw8841step0 = injectiveMoment H raw8841step1 := by
      have heq : raw8841step1 = (fun i j => raw8841step0 (permutation379 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8841step0 permutation379 permutation9
    _ = injectiveMoment H node2900 := by rfl

def raw8842 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8842step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8842step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical8842 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8842 = injectiveMoment H node3454 := by
  calc
    injectiveMoment H raw8842 = injectiveMoment H raw8842step0 := by
      have heq : raw8842step0 = -raw8842 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8842).symm
    injectiveMoment H raw8842step0 = injectiveMoment H raw8842step1 := by
      have heq : raw8842step1 = (fun i j => raw8842step0 (permutation256 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8842step0 permutation256 permutation15
    _ = injectiveMoment H node3454 := by rfl

def raw8843 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 1, -3]]

def raw8843step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

theorem canonical8843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8843 = injectiveMoment H node3431 := by
  calc
    injectiveMoment H raw8843 = injectiveMoment H raw8843step0 := by
      have heq : raw8843step0 = (fun i j => raw8843 (permutation182 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8843 permutation182 permutation16
    _ = injectiveMoment H node3431 := by rfl

def raw8844 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -1, 2, -3]]

def raw8844step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 1, -2, 3]]

def raw8844step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical8844 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8844 = injectiveMoment H node3229 := by
  calc
    injectiveMoment H raw8844 = injectiveMoment H raw8844step0 := by
      have heq : raw8844step0 = -raw8844 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8844).symm
    injectiveMoment H raw8844step0 = injectiveMoment H raw8844step1 := by
      have heq : raw8844step1 = (fun i j => raw8844step0 (permutation379 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8844step0 permutation379 permutation9
    _ = injectiveMoment H node3229 := by rfl

def raw8845 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8845step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8845step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical8845 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8845 = injectiveMoment H node2933 := by
  calc
    injectiveMoment H raw8845 = injectiveMoment H raw8845step0 := by
      have heq : raw8845step0 = -raw8845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8845).symm
    injectiveMoment H raw8845step0 = injectiveMoment H raw8845step1 := by
      have heq : raw8845step1 = (fun i j => raw8845step0 (permutation342 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8845step0 permutation342 permutation15
    _ = injectiveMoment H node2933 := by rfl

def raw8846 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8846step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical8846 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8846 = injectiveMoment H node3277 := by
  calc
    injectiveMoment H raw8846 = injectiveMoment H raw8846step0 := by
      have heq : raw8846step0 = (fun i j => raw8846 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8846 permutation258 permutation9
    _ = injectiveMoment H node3277 := by rfl

def raw8847 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![1, 2, 1, -4]]

def raw8847step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 1, -1, -2], ![-1, -2, -1, 4]]

def raw8847step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem canonical8847 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8847 = injectiveMoment H node2905 := by
  calc
    injectiveMoment H raw8847 = injectiveMoment H raw8847step0 := by
      have heq : raw8847step0 = -raw8847 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8847).symm
    injectiveMoment H raw8847step0 = injectiveMoment H raw8847step1 := by
      have heq : raw8847step1 = (fun i j => raw8847step0 (permutation379 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8847step0 permutation379 permutation15
    _ = injectiveMoment H node2905 := by rfl

def raw8848 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8848step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![-1, -1, -2, 4]]

def raw8848step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical8848 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8848 = injectiveMoment H node3349 := by
  calc
    injectiveMoment H raw8848 = injectiveMoment H raw8848step0 := by
      have heq : raw8848step0 = -raw8848 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8848).symm
    injectiveMoment H raw8848step0 = injectiveMoment H raw8848step1 := by
      have heq : raw8848step1 = (fun i j => raw8848step0 (permutation380 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8848step0 permutation380 permutation15
    _ = injectiveMoment H node3349 := by rfl

def raw8849 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 1, -3]]

def raw8849step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -1, -1, 3]]

def raw8849step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical8849 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8849 = injectiveMoment H node3372 := by
  calc
    injectiveMoment H raw8849 = injectiveMoment H raw8849step0 := by
      have heq : raw8849step0 = -raw8849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8849).symm
    injectiveMoment H raw8849step0 = injectiveMoment H raw8849step1 := by
      have heq : raw8849step1 = (fun i j => raw8849step0 (permutation380 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8849step0 permutation380 permutation15
    _ = injectiveMoment H node3372 := by rfl

def raw8850 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 2, -3]]

def raw8850step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical8850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8850 = injectiveMoment H node3452 := by
  calc
    injectiveMoment H raw8850 = injectiveMoment H raw8850step0 := by
      have heq : raw8850step0 = (fun i j => raw8850 (permutation155 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8850 permutation155 permutation16
    _ = injectiveMoment H node3452 := by rfl

def raw8851 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8851step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8851step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical8851 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8851 = injectiveMoment H node3454 := by
  calc
    injectiveMoment H raw8851 = injectiveMoment H raw8851step0 := by
      have heq : raw8851step0 = -raw8851 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8851).symm
    injectiveMoment H raw8851step0 = injectiveMoment H raw8851step1 := by
      have heq : raw8851step1 = (fun i j => raw8851step0 (permutation237 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8851step0 permutation237 permutation15
    _ = injectiveMoment H node3454 := by rfl

def raw8852 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 0, 2, -4]]

def raw8852step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

theorem canonical8852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8852 = injectiveMoment H node2960 := by
  calc
    injectiveMoment H raw8852 = injectiveMoment H raw8852step0 := by
      have heq : raw8852step0 = (fun i j => raw8852 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8852 permutation258 permutation9
    _ = injectiveMoment H node2960 := by rfl

def raw8853 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -1, 2, -3]]

def raw8853step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem canonical8853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8853 = injectiveMoment H node3171 := by
  calc
    injectiveMoment H raw8853 = injectiveMoment H raw8853step0 := by
      have heq : raw8853step0 = (fun i j => raw8853 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8853 permutation258 permutation9
    _ = injectiveMoment H node3171 := by rfl

def raw8854 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8854step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical8854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8854 = injectiveMoment H node3172 := by
  calc
    injectiveMoment H raw8854 = injectiveMoment H raw8854step0 := by
      have heq : raw8854step0 = (fun i j => raw8854 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8854 permutation258 permutation9
    _ = injectiveMoment H node3172 := by rfl

def raw8855 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![1, 1, 2, -4]]

def raw8855step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8855 = injectiveMoment H node2961 := by
  calc
    injectiveMoment H raw8855 = injectiveMoment H raw8855step0 := by
      have heq : raw8855step0 = (fun i j => raw8855 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8855 permutation258 permutation9
    _ = injectiveMoment H node2961 := by rfl

def raw8856 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 2, -3]]

def raw8856step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical8856 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8856 = injectiveMoment H node3438 := by
  calc
    injectiveMoment H raw8856 = injectiveMoment H raw8856step0 := by
      have heq : raw8856step0 = (fun i j => raw8856 (permutation186 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8856 permutation186 permutation16
    _ = injectiveMoment H node3438 := by rfl

def raw8857 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -1, -2, 3]]

def raw8857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 1, 2, -3]]

def raw8857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![-2, -2, 4], ![1, 2, -3]]

def raw8857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8857 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8857 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw8857 = injectiveMoment H raw8857step0 := by
      have heq : raw8857step0 = -raw8857 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8857).symm
    injectiveMoment H raw8857step0 = injectiveMoment H raw8857step1 := by
      have hz : ∀ i, raw8857step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8857step1 = (fun i j => raw8857step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8857step0 permutation9 hz
    injectiveMoment H raw8857step1 = injectiveMoment H raw8857step2 := by
      have heq : raw8857step2 = (fun i j => raw8857step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8857step1 permutation23 permutation3
    _ = injectiveMoment H node149 := by rfl

def raw8858 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8858step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8858step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical8858 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8858 = injectiveMoment H node3115 := by
  calc
    injectiveMoment H raw8858 = injectiveMoment H raw8858step0 := by
      have heq : raw8858step0 = -raw8858 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8858).symm
    injectiveMoment H raw8858step0 = injectiveMoment H raw8858step1 := by
      have heq : raw8858step1 = (fun i j => raw8858step0 (permutation382 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8858step0 permutation382 permutation15
    _ = injectiveMoment H node3115 := by rfl

def raw8859 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8859step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8859step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical8859 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8859 = injectiveMoment H node3115 := by
  calc
    injectiveMoment H raw8859 = injectiveMoment H raw8859step0 := by
      have heq : raw8859step0 = -raw8859 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8859).symm
    injectiveMoment H raw8859step0 = injectiveMoment H raw8859step1 := by
      have heq : raw8859step1 = (fun i j => raw8859step0 (permutation362 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8859step0 permutation362 permutation15
    _ = injectiveMoment H node3115 := by rfl

def raw8860 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 2, 2, -4]]

def raw8860step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical8860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8860 = injectiveMoment H node2963 := by
  calc
    injectiveMoment H raw8860 = injectiveMoment H raw8860step0 := by
      have heq : raw8860step0 = (fun i j => raw8860 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8860 permutation262 permutation9
    _ = injectiveMoment H node2963 := by rfl

def raw8861 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw8861step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw8861step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical8861 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8861 = injectiveMoment H node3416 := by
  calc
    injectiveMoment H raw8861 = injectiveMoment H raw8861step0 := by
      have heq : raw8861step0 = -raw8861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8861).symm
    injectiveMoment H raw8861step0 = injectiveMoment H raw8861step1 := by
      have heq : raw8861step1 = (fun i j => raw8861step0 (permutation365 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8861step0 permutation365 permutation15
    _ = injectiveMoment H node3416 := by rfl

def raw8862 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8862step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 1, 2, -2]]

def raw8862step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical8862 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8862 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw8862 = injectiveMoment H raw8862step0 := by
      have heq : raw8862step0 = -raw8862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8862).symm
    injectiveMoment H raw8862step0 = injectiveMoment H raw8862step1 := by
      have heq : raw8862step1 = (fun i j => raw8862step0 (permutation132 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8862step0 permutation132 permutation13
    _ = injectiveMoment H node2449 := by rfl

def raw8863 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8863step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![0, -1, -1, 2]]

def raw8863step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![0, 1, 1, -2]]

def raw8863step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical8863 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8863 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw8863 = injectiveMoment H raw8863step0 := by
      have heq : raw8863step0 = raw8863.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8863).symm
    injectiveMoment H raw8863step0 = injectiveMoment H raw8863step1 := by
      have heq : raw8863step1 = -raw8863step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8863step0).symm
    injectiveMoment H raw8863step1 = injectiveMoment H raw8863step2 := by
      have heq : raw8863step2 = (fun i j => raw8863step1 (permutation21 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8863step1 permutation21 permutation15
    _ = injectiveMoment H node1047 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
