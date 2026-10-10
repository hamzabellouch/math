import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6816 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1]]

def raw6816step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6816 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6816 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw6816 = injectiveMoment H raw6816step0 := by
      have hz : ∀ j, raw6816 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw6816step0 = (fun i j => raw6816 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6816 permutation104 hz
    _ = injectiveMoment H node284 := by rfl

def raw6817 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1]]

def raw6817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6817 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H raw6817 = injectiveMoment H raw6817step0 := by
      have heq : raw6817step0 = (fun i j => raw6817 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6817 permutation37 permutation3
    _ = injectiveMoment H node1152 := by rfl

def raw6818 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6818 = injectiveMoment H node284 := by
  rfl

def raw6819 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1]]

def raw6819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical6819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6819 = injectiveMoment H node1149 := by
  calc
    injectiveMoment H raw6819 = injectiveMoment H raw6819step0 := by
      have heq : raw6819step0 = (fun i j => raw6819 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6819 permutation35 permutation3
    _ = injectiveMoment H node1149 := by rfl

def raw6820 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical6820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6820 = injectiveMoment H node285 := by
  rfl

def raw6821 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![0, 0, 0]]

def raw6821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical6821 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6821 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6821 = injectiveMoment H raw6821step0 := by
      have hz : ∀ j, raw6821 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw6821step0 = (fun i j => raw6821 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6821 permutation128 hz
    _ = injectiveMoment H node285 := by rfl

def raw6822 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![0, -1, 1], ![1, -1, 0]]

def raw6822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical6822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6822 = injectiveMoment H node1150 := by
  calc
    injectiveMoment H raw6822 = injectiveMoment H raw6822step0 := by
      have heq : raw6822step0 = (fun i j => raw6822 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6822 permutation35 permutation3
    _ = injectiveMoment H node1150 := by rfl

def raw6823 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

theorem canonical6823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6823 = injectiveMoment H node286 := by
  rfl

def raw6824 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![0, -1, 1]]

def raw6824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical6824 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6824 = injectiveMoment H node1150 := by
  calc
    injectiveMoment H raw6824 = injectiveMoment H raw6824step0 := by
      have heq : raw6824step0 = (fun i j => raw6824 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6824 permutation37 permutation3
    _ = injectiveMoment H node1150 := by rfl

def raw6825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def raw6825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6825 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6825 = injectiveMoment H node2294 := by
  calc
    injectiveMoment H raw6825 = injectiveMoment H raw6825step0 := by
      have heq : raw6825step0 = (fun i j => raw6825 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6825 permutation258 permutation3
    _ = injectiveMoment H node2294 := by rfl

def raw6826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def raw6826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6826 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6826 = injectiveMoment H node2650 := by
  calc
    injectiveMoment H raw6826 = injectiveMoment H raw6826step0 := by
      have heq : raw6826step0 = (fun i j => raw6826 (permutation185 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6826 permutation185 permutation3
    _ = injectiveMoment H node2650 := by rfl

def raw6827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1]]

def raw6827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6827 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6827 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw6827 = injectiveMoment H raw6827step0 := by
      have heq : raw6827step0 = (fun i j => raw6827 (permutation36 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6827 permutation36 permutation3
    _ = injectiveMoment H node1151 := by rfl

def raw6828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw6828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6828 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6828 = injectiveMoment H node2649 := by
  calc
    injectiveMoment H raw6828 = injectiveMoment H raw6828step0 := by
      have heq : raw6828step0 = (fun i j => raw6828 (permutation185 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6828 permutation185 permutation3
    _ = injectiveMoment H node2649 := by rfl

def raw6829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6829 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6829 = injectiveMoment H raw6829step0 := by
      have hz : ∀ j, raw6829 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw6829step0 = (fun i j => raw6829 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6829 permutation57 hz
    _ = injectiveMoment H node287 := by rfl

def raw6830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]

def raw6830step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6830 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6830 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw6830 = injectiveMoment H raw6830step0 := by
      have hz : ∀ j, raw6830 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw6830step0 = (fun i j => raw6830 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6830 permutation15 hz
    _ = injectiveMoment H node61 := by rfl

def raw6831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]

def raw6831step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6831 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6831 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw6831 = injectiveMoment H raw6831step0 := by
      have hz : ∀ j, raw6831 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw6831step0 = (fun i j => raw6831 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6831 permutation15 hz
    _ = injectiveMoment H node62 := by rfl

def raw6832 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![1, 1, -2]]

def raw6832step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]

def raw6832step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw6832step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical6832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6832 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6832 = injectiveMoment H raw6832step0 := by
      have heq : raw6832step0 = raw6832.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6832).symm
    injectiveMoment H raw6832step0 = injectiveMoment H raw6832step1 := by
      have hz : ∀ i, raw6832step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw6832step1 = (fun i j => raw6832step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6832step0 permutation5 hz
    injectiveMoment H raw6832step1 = injectiveMoment H raw6832step2 := by
      have heq : raw6832step2 = (fun i j => raw6832step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6832step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw6833 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]

def raw6833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6833 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H raw6833 = injectiveMoment H raw6833step0 := by
      have heq : raw6833step0 = (fun i j => raw6833 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6833 permutation39 permutation3
    _ = injectiveMoment H node1141 := by rfl

def raw6834 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw6834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw6834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6834 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6834 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw6834 = injectiveMoment H raw6834step0 := by
      have heq : raw6834step0 = -raw6834 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6834).symm
    injectiveMoment H raw6834step0 = injectiveMoment H raw6834step1 := by
      have heq : raw6834step1 = (fun i j => raw6834step0 (permutation48 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6834step0 permutation48 permutation7
    _ = injectiveMoment H node711 := by rfl

def raw6835 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1]]

def raw6835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, -1, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1]]

def raw6835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6835 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6835 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H raw6835 = injectiveMoment H raw6835step0 := by
      have heq : raw6835step0 = -raw6835 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6835).symm
    injectiveMoment H raw6835step0 = injectiveMoment H raw6835step1 := by
      have heq : raw6835step1 = (fun i j => raw6835step0 (permutation124 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6835step0 permutation124 permutation4
    _ = injectiveMoment H node1141 := by rfl

def raw6836 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]

def raw6836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw6836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6836 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6836 = injectiveMoment H node709 := by
  calc
    injectiveMoment H raw6836 = injectiveMoment H raw6836step0 := by
      have heq : raw6836step0 = -raw6836 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6836).symm
    injectiveMoment H raw6836step0 = injectiveMoment H raw6836step1 := by
      have heq : raw6836step1 = (fun i j => raw6836step0 (permutation49 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6836step0 permutation49 permutation7
    _ = injectiveMoment H node709 := by rfl

def raw6837 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2]]

def raw6837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical6837 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6837 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw6837 = injectiveMoment H raw6837step0 := by
      have heq : raw6837step0 = (fun i j => raw6837 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6837 permutation11 permutation3
    _ = injectiveMoment H node283 := by rfl

def raw6838 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]

def raw6838step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6838 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6838 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6838 = injectiveMoment H raw6838step0 := by
      have hz : ∀ j, raw6838 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw6838step0 = (fun i j => raw6838 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6838 permutation80 hz
    _ = injectiveMoment H node287 := by rfl

def raw6839 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]

def raw6839step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6839 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw6839 = injectiveMoment H raw6839step0 := by
      have hz : ∀ j, raw6839 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw6839step0 = (fun i j => raw6839 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6839 permutation21 hz
    _ = injectiveMoment H node61 := by rfl

def raw6840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2]]

def raw6840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical6840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6840 = injectiveMoment H node1146 := by
  calc
    injectiveMoment H raw6840 = injectiveMoment H raw6840step0 := by
      have heq : raw6840step0 = (fun i j => raw6840 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6840 permutation45 permutation3
    _ = injectiveMoment H node1146 := by rfl

def raw6841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw6841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6841 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw6841 = injectiveMoment H raw6841step0 := by
      have heq : raw6841step0 = (fun i j => raw6841 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6841 permutation45 permutation3
    _ = injectiveMoment H node1151 := by rfl

def raw6842 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]

def raw6842step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6842 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6842 = injectiveMoment H raw6842step0 := by
      have hz : ∀ j, raw6842 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw6842step0 = (fun i j => raw6842 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6842 permutation104 hz
    _ = injectiveMoment H node287 := by rfl

def raw6843 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

theorem canonical6843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6843 = injectiveMoment H node1153 := by
  rfl

def raw6844 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1]]

def raw6844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

theorem canonical6844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6844 = injectiveMoment H node1153 := by
  calc
    injectiveMoment H raw6844 = injectiveMoment H raw6844step0 := by
      have heq : raw6844step0 = (fun i j => raw6844 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6844 permutation34 permutation3
    _ = injectiveMoment H node1153 := by rfl

def raw6845 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6845 = injectiveMoment H node287 := by
  rfl

def raw6846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def raw6846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical6846 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6846 = injectiveMoment H node1849 := by
  calc
    injectiveMoment H raw6846 = injectiveMoment H raw6846step0 := by
      have heq : raw6846step0 = (fun i j => raw6846 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6846 permutation258 permutation3
    _ = injectiveMoment H node1849 := by rfl

def raw6847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw6847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical6847 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6847 = injectiveMoment H node2456 := by
  calc
    injectiveMoment H raw6847 = injectiveMoment H raw6847step0 := by
      have heq : raw6847step0 = (fun i j => raw6847 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6847 permutation258 permutation3
    _ = injectiveMoment H node2456 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
