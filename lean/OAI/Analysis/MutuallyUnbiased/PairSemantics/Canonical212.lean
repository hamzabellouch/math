import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6784 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1]]

def raw6784step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical6784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6784 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw6784 = injectiveMoment H raw6784step0 := by
      have hz : ∀ j, raw6784 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw6784step0 = (fun i j => raw6784 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6784 permutation104 hz
    _ = injectiveMoment H node280 := by rfl

def raw6785 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![0, 1, -1]]

def raw6785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical6785 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6785 = injectiveMoment H node1148 := by
  calc
    injectiveMoment H raw6785 = injectiveMoment H raw6785step0 := by
      have heq : raw6785step0 = (fun i j => raw6785 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6785 permutation37 permutation3
    _ = injectiveMoment H node1148 := by rfl

def raw6786 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical6786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6786 = injectiveMoment H node280 := by
  rfl

def raw6787 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![0, 0, 0]]

def raw6787step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical6787 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6787 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw6787 = injectiveMoment H raw6787step0 := by
      have hz : ∀ j, raw6787 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw6787step0 = (fun i j => raw6787 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6787 permutation128 hz
    _ = injectiveMoment H node280 := by rfl

def raw6788 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical6788 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6788 = injectiveMoment H node281 := by
  rfl

def raw6789 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![1, 3, -4]]

def raw6789step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw6789step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical6789 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6789 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw6789 = injectiveMoment H raw6789step0 := by
      have heq : raw6789step0 = -raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6789).symm
    injectiveMoment H raw6789step0 = injectiveMoment H raw6789step1 := by
      have heq : raw6789step1 = (fun i j => raw6789step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6789step0 permutation8 permutation3
    _ = injectiveMoment H node52 := by rfl

def raw6790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2]]

def raw6790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]

def raw6790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6790 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6790 = injectiveMoment H node659 := by
  calc
    injectiveMoment H raw6790 = injectiveMoment H raw6790step0 := by
      have heq : raw6790step0 = -raw6790 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6790).symm
    injectiveMoment H raw6790step0 = injectiveMoment H raw6790step1 := by
      have heq : raw6790step1 = (fun i j => raw6790step0 (permutation148 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6790step0 permutation148 permutation3
    _ = injectiveMoment H node659 := by rfl

def raw6791 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw6791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6791 = injectiveMoment H node1135 := by
  calc
    injectiveMoment H raw6791 = injectiveMoment H raw6791step0 := by
      have heq : raw6791step0 = (fun i j => raw6791 (permutation35 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6791 permutation35 permutation5
    _ = injectiveMoment H node1135 := by rfl

def raw6792 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1]]

def raw6792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6792 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6792 = injectiveMoment H node1135 := by
  calc
    injectiveMoment H raw6792 = injectiveMoment H raw6792step0 := by
      have heq : raw6792step0 = (fun i j => raw6792 (permutation37 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6792 permutation37 permutation5
    _ = injectiveMoment H node1135 := by rfl

def raw6793 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2]]

def raw6793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6793 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6793 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H raw6793 = injectiveMoment H raw6793step0 := by
      have heq : raw6793step0 = -raw6793 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6793).symm
    injectiveMoment H raw6793step0 = injectiveMoment H raw6793step1 := by
      have heq : raw6793step1 = (fun i j => raw6793step0 (permutation148 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6793step0 permutation148 permutation3
    _ = injectiveMoment H node1141 := by rfl

def raw6794 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6794 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw6794 = injectiveMoment H raw6794step0 := by
      have heq : raw6794step0 = (fun i j => raw6794 (permutation81 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6794 permutation81 permutation4
    _ = injectiveMoment H node872 := by rfl

def raw6795 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0]]

def raw6795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6795 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6795 = injectiveMoment H node742 := by
  calc
    injectiveMoment H raw6795 = injectiveMoment H raw6795step0 := by
      have heq : raw6795step0 = (fun i j => raw6795 (permutation80 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6795 permutation80 permutation4
    _ = injectiveMoment H node742 := by rfl

def raw6796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

def raw6796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

theorem canonical6796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6796 = injectiveMoment H node1145 := by
  calc
    injectiveMoment H raw6796 = injectiveMoment H raw6796step0 := by
      have heq : raw6796step0 = (fun i j => raw6796 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6796 permutation39 permutation3
    _ = injectiveMoment H node1145 := by rfl

def raw6797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def raw6797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![-2, -1, 3]]

def raw6797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

theorem canonical6797 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6797 = injectiveMoment H node1889 := by
  calc
    injectiveMoment H raw6797 = injectiveMoment H raw6797step0 := by
      have heq : raw6797step0 = -raw6797 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6797).symm
    injectiveMoment H raw6797step0 = injectiveMoment H raw6797step1 := by
      have heq : raw6797step1 = (fun i j => raw6797step0 (permutation340 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6797step0 permutation340 permutation3
    _ = injectiveMoment H node1889 := by rfl

def raw6798 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical6798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6798 = injectiveMoment H node1149 := by
  rfl

def raw6799 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical6799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6799 = injectiveMoment H node1150 := by
  rfl

def raw6800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def raw6800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]

def raw6800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical6800 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6800 = injectiveMoment H node1862 := by
  calc
    injectiveMoment H raw6800 = injectiveMoment H raw6800step0 := by
      have heq : raw6800step0 = -raw6800 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6800).symm
    injectiveMoment H raw6800step0 = injectiveMoment H raw6800step1 := by
      have heq : raw6800step1 = (fun i j => raw6800step0 (permutation379 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6800step0 permutation379 permutation3
    _ = injectiveMoment H node1862 := by rfl

def raw6801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def raw6801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6801 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6801 = injectiveMoment H node2382 := by
  calc
    injectiveMoment H raw6801 = injectiveMoment H raw6801step0 := by
      have heq : raw6801step0 = (fun i j => raw6801 (permutation309 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6801 permutation309 permutation4
    _ = injectiveMoment H node2382 := by rfl

def raw6802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def raw6802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6802 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6802 = injectiveMoment H node2671 := by
  calc
    injectiveMoment H raw6802 = injectiveMoment H raw6802step0 := by
      have heq : raw6802step0 = (fun i j => raw6802 (permutation197 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6802 permutation197 permutation3
    _ = injectiveMoment H node2671 := by rfl

def raw6803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def raw6803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical6803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6803 = injectiveMoment H node1532 := by
  calc
    injectiveMoment H raw6803 = injectiveMoment H raw6803step0 := by
      have heq : raw6803step0 = (fun i j => raw6803 (permutation308 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6803 permutation308 permutation4
    _ = injectiveMoment H node1532 := by rfl

def raw6804 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2]]

def raw6804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical6804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6804 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw6804 = injectiveMoment H raw6804step0 := by
      have hz : ∀ j, raw6804 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw6804step0 = (fun i j => raw6804 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6804 permutation80 hz
    _ = injectiveMoment H node283 := by rfl

def raw6805 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1]]

def raw6805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6805 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw6805 = injectiveMoment H raw6805step0 := by
      have hz : ∀ j, raw6805 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw6805step0 = (fun i j => raw6805 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6805 permutation80 hz
    _ = injectiveMoment H node284 := by rfl

def raw6806 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2]]

def raw6806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical6806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6806 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw6806 = injectiveMoment H raw6806step0 := by
      have hz : ∀ j, raw6806 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw6806step0 = (fun i j => raw6806 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6806 permutation104 hz
    _ = injectiveMoment H node283 := by rfl

def raw6807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6807 = injectiveMoment H node1151 := by
  rfl

def raw6808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6808 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6808 = injectiveMoment H node1152 := by
  rfl

def raw6809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def raw6809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![-2, -2, 4]]

def raw6809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6809 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6809 = injectiveMoment H node1528 := by
  calc
    injectiveMoment H raw6809 = injectiveMoment H raw6809step0 := by
      have heq : raw6809step0 = -raw6809 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6809).symm
    injectiveMoment H raw6809step0 = injectiveMoment H raw6809step1 := by
      have heq : raw6809step1 = (fun i j => raw6809step0 (permutation372 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6809step0 permutation372 permutation5
    _ = injectiveMoment H node1528 := by rfl

def raw6810 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 2, -2]]

def raw6810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6810 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6810 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H raw6810 = injectiveMoment H raw6810step0 := by
      have heq : raw6810step0 = (fun i j => raw6810 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6810 permutation34 permutation3
    _ = injectiveMoment H node1152 := by rfl

def raw6811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def raw6811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6811 = injectiveMoment H node2669 := by
  calc
    injectiveMoment H raw6811 = injectiveMoment H raw6811step0 := by
      have heq : raw6811step0 = (fun i j => raw6811 (permutation197 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6811 permutation197 permutation3
    _ = injectiveMoment H node2669 := by rfl

def raw6812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def raw6812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw6812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6812 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6812 = injectiveMoment H node2459 := by
  calc
    injectiveMoment H raw6812 = injectiveMoment H raw6812step0 := by
      have heq : raw6812step0 = -raw6812 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6812).symm
    injectiveMoment H raw6812step0 = injectiveMoment H raw6812step1 := by
      have heq : raw6812step1 = (fun i j => raw6812step0 (permutation385 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6812step0 permutation385 permutation3
    _ = injectiveMoment H node2459 := by rfl

def raw6813 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1]]

def raw6813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6813 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6813 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw6813 = injectiveMoment H raw6813step0 := by
      have heq : raw6813step0 = (fun i j => raw6813 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6813 permutation34 permutation3
    _ = injectiveMoment H node1151 := by rfl

def raw6814 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical6814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6814 = injectiveMoment H node283 := by
  rfl

def raw6815 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2]]

def raw6815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![-1, -1, 2]]

def raw6815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical6815 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6815 = injectiveMoment H node1146 := by
  calc
    injectiveMoment H raw6815 = injectiveMoment H raw6815step0 := by
      have heq : raw6815step0 = -raw6815 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6815).symm
    injectiveMoment H raw6815step0 = injectiveMoment H raw6815step1 := by
      have heq : raw6815step1 = (fun i j => raw6815step0 (permutation142 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6815step0 permutation142 permutation3
    _ = injectiveMoment H node1146 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
