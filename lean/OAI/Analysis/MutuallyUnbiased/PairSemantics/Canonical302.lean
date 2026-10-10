import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9664 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9664step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw9664step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9664 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9664 = injectiveMoment H node2955 := by
  calc
    injectiveMoment H raw9664 = injectiveMoment H raw9664step0 := by
      have heq : raw9664step0 = -raw9664 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9664).symm
    injectiveMoment H raw9664step0 = injectiveMoment H raw9664step1 := by
      have heq : raw9664step1 = (fun i j => raw9664step0 (permutation342 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9664step0 permutation342 permutation23
    _ = injectiveMoment H node2955 := by rfl

def raw9665 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, -1, 2], ![0, -1, 3, -2]]

def raw9665step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9665 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9665 = injectiveMoment H node3252 := by
  calc
    injectiveMoment H raw9665 = injectiveMoment H raw9665step0 := by
      have heq : raw9665step0 = (fun i j => raw9665 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9665 permutation294 permutation9
    _ = injectiveMoment H node3252 := by rfl

def raw9666 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 2, -1]]

def raw9666step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9666 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9666 = injectiveMoment H node3206 := by
  calc
    injectiveMoment H raw9666 = injectiveMoment H raw9666step0 := by
      have heq : raw9666step0 = (fun i j => raw9666 (permutation263 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9666 permutation263 permutation11
    _ = injectiveMoment H node3206 := by rfl

def raw9667 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 1, 3, -3]]

def raw9667step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

theorem canonical9667 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9667 = injectiveMoment H node3366 := by
  calc
    injectiveMoment H raw9667 = injectiveMoment H raw9667step0 := by
      have heq : raw9667step0 = (fun i j => raw9667 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9667 permutation285 permutation15
    _ = injectiveMoment H node3366 := by rfl

def raw9668 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9668step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9668step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9668 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9668 = injectiveMoment H node3036 := by
  calc
    injectiveMoment H raw9668 = injectiveMoment H raw9668step0 := by
      have heq : raw9668step0 = -raw9668 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9668).symm
    injectiveMoment H raw9668step0 = injectiveMoment H raw9668step1 := by
      have heq : raw9668step1 = (fun i j => raw9668step0 (permutation342 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9668step0 permutation342 permutation23
    _ = injectiveMoment H node3036 := by rfl

def raw9669 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9669step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9669 = injectiveMoment H node3232 := by
  calc
    injectiveMoment H raw9669 = injectiveMoment H raw9669step0 := by
      have heq : raw9669step0 = (fun i j => raw9669 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9669 permutation395 permutation10
    _ = injectiveMoment H node3232 := by rfl

def raw9670 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, 1, 2, -3]]

def raw9670step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9670 = injectiveMoment H node2898 := by
  calc
    injectiveMoment H raw9670 = injectiveMoment H raw9670step0 := by
      have heq : raw9670step0 = (fun i j => raw9670 (permutation262 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9670 permutation262 permutation11
    _ = injectiveMoment H node2898 := by rfl

def raw9671 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 1, -2]]

def raw9671step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![0, -1, -1, 2]]

def raw9671step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical9671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9671 = injectiveMoment H node3388 := by
  calc
    injectiveMoment H raw9671 = injectiveMoment H raw9671step0 := by
      have heq : raw9671step0 = -raw9671 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9671).symm
    injectiveMoment H raw9671step0 = injectiveMoment H raw9671step1 := by
      have heq : raw9671step1 = (fun i j => raw9671step0 (permutation346 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9671step0 permutation346 permutation23
    _ = injectiveMoment H node3388 := by rfl

def raw9672 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9672step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -1, -2, 2]]

def raw9672step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem canonical9672 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9672 = injectiveMoment H node3022 := by
  calc
    injectiveMoment H raw9672 = injectiveMoment H raw9672step0 := by
      have heq : raw9672step0 = -raw9672 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9672).symm
    injectiveMoment H raw9672step0 = injectiveMoment H raw9672step1 := by
      have heq : raw9672step1 = (fun i j => raw9672step0 (permutation345 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9672step0 permutation345 permutation23
    _ = injectiveMoment H node3022 := by rfl

def raw9673 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 1, -1]]

def raw9673step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -1, 1]]

def raw9673step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical9673 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9673 = injectiveMoment H node3403 := by
  calc
    injectiveMoment H raw9673 = injectiveMoment H raw9673step0 := by
      have heq : raw9673step0 = -raw9673 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9673).symm
    injectiveMoment H raw9673step0 = injectiveMoment H raw9673step1 := by
      have heq : raw9673step1 = (fun i j => raw9673step0 (permutation346 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9673step0 permutation346 permutation23
    _ = injectiveMoment H node3403 := by rfl

def raw9674 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -2, 3], ![-2, 1, 3, -2]]

def raw9674step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9674 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9674 = injectiveMoment H node3303 := by
  calc
    injectiveMoment H raw9674 = injectiveMoment H raw9674step0 := by
      have heq : raw9674step0 = (fun i j => raw9674 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9674 permutation395 permutation9
    _ = injectiveMoment H node3303 := by rfl

def raw9675 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 2, -1]]

def raw9675step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw9675step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical9675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9675 = injectiveMoment H node3091 := by
  calc
    injectiveMoment H raw9675 = injectiveMoment H raw9675step0 := by
      have heq : raw9675step0 = -raw9675 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9675).symm
    injectiveMoment H raw9675step0 = injectiveMoment H raw9675step1 := by
      have heq : raw9675step1 = (fun i j => raw9675step0 (permutation345 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9675step0 permutation345 permutation23
    _ = injectiveMoment H node3091 := by rfl

def raw9676 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9676step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem canonical9676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9676 = injectiveMoment H node3146 := by
  calc
    injectiveMoment H raw9676 = injectiveMoment H raw9676step0 := by
      have heq : raw9676step0 = (fun i j => raw9676 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9676 permutation323 permutation16
    _ = injectiveMoment H node3146 := by rfl

def raw9677 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9677step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9677 = injectiveMoment H node3084 := by
  calc
    injectiveMoment H raw9677 = injectiveMoment H raw9677step0 := by
      have heq : raw9677step0 = (fun i j => raw9677 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9677 permutation323 permutation16
    _ = injectiveMoment H node3084 := by rfl

def raw9678 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9678step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical9678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9678 = injectiveMoment H node3183 := by
  calc
    injectiveMoment H raw9678 = injectiveMoment H raw9678step0 := by
      have heq : raw9678step0 = (fun i j => raw9678 (permutation267 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9678 permutation267 permutation15
    _ = injectiveMoment H node3183 := by rfl

def raw9679 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9679step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical9679 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9679 = injectiveMoment H node3215 := by
  calc
    injectiveMoment H raw9679 = injectiveMoment H raw9679step0 := by
      have heq : raw9679step0 = (fun i j => raw9679 (permutation267 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9679 permutation267 permutation15
    _ = injectiveMoment H node3215 := by rfl

def raw9680 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9680step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9680 = injectiveMoment H node3001 := by
  calc
    injectiveMoment H raw9680 = injectiveMoment H raw9680step0 := by
      have heq : raw9680step0 = (fun i j => raw9680 (permutation363 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9680 permutation363 permutation19
    _ = injectiveMoment H node3001 := by rfl

def raw9681 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9681step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9681 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9681 = injectiveMoment H node3085 := by
  calc
    injectiveMoment H raw9681 = injectiveMoment H raw9681step0 := by
      have heq : raw9681step0 = (fun i j => raw9681 (permutation317 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9681 permutation317 permutation16
    _ = injectiveMoment H node3085 := by rfl

def raw9682 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9682step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical9682 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9682 = injectiveMoment H node3187 := by
  calc
    injectiveMoment H raw9682 = injectiveMoment H raw9682step0 := by
      have heq : raw9682step0 = (fun i j => raw9682 (permutation267 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9682 permutation267 permutation15
    _ = injectiveMoment H node3187 := by rfl

def raw9683 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9683step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9683 = injectiveMoment H node3042 := by
  calc
    injectiveMoment H raw9683 = injectiveMoment H raw9683step0 := by
      have heq : raw9683step0 = (fun i j => raw9683 (permutation349 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9683 permutation349 permutation13
    _ = injectiveMoment H node3042 := by rfl

def raw9684 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![0, -2, 3, -1]]

def raw9684step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical9684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9684 = injectiveMoment H node3144 := by
  calc
    injectiveMoment H raw9684 = injectiveMoment H raw9684step0 := by
      have heq : raw9684step0 = (fun i j => raw9684 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9684 permutation323 permutation16
    _ = injectiveMoment H node3144 := by rfl

def raw9685 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 2, 0]]

def raw9685step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9685 = injectiveMoment H node3174 := by
  calc
    injectiveMoment H raw9685 = injectiveMoment H raw9685step0 := by
      have heq : raw9685step0 = (fun i j => raw9685 (permutation383 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9685 permutation383 permutation19
    _ = injectiveMoment H node3174 := by rfl

def raw9686 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![-1, -2, 2, 1]]

def raw9686step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9686 = injectiveMoment H node3083 := by
  calc
    injectiveMoment H raw9686 = injectiveMoment H raw9686step0 := by
      have heq : raw9686step0 = (fun i j => raw9686 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9686 permutation323 permutation16
    _ = injectiveMoment H node3083 := by rfl

def raw9687 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 1, 2]]

def raw9687step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9687 = injectiveMoment H node3076 := by
  calc
    injectiveMoment H raw9687 = injectiveMoment H raw9687step0 := by
      have heq : raw9687step0 = (fun i j => raw9687 (permutation317 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9687 permutation317 permutation15
    _ = injectiveMoment H node3076 := by rfl

def raw9688 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, -1, 3], ![-2, 1, 3, -2]]

def raw9688step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical9688 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9688 = injectiveMoment H node3132 := by
  calc
    injectiveMoment H raw9688 = injectiveMoment H raw9688step0 := by
      have heq : raw9688step0 = (fun i j => raw9688 (permutation267 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9688 permutation267 permutation15
    _ = injectiveMoment H node3132 := by rfl

def raw9689 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 2, -1]]

def raw9689step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def raw9689step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9689 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9689 = injectiveMoment H node3095 := by
  calc
    injectiveMoment H raw9689 = injectiveMoment H raw9689step0 := by
      have heq : raw9689step0 = -raw9689 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9689).symm
    injectiveMoment H raw9689step0 = injectiveMoment H raw9689step1 := by
      have heq : raw9689step1 = (fun i j => raw9689step0 (permutation348 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9689step0 permutation348 permutation23
    _ = injectiveMoment H node3095 := by rfl

def raw9690 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 1, 0]]

def raw9690step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9690 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9690 = injectiveMoment H node3210 := by
  calc
    injectiveMoment H raw9690 = injectiveMoment H raw9690step0 := by
      have heq : raw9690step0 = (fun i j => raw9690 (permutation336 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9690 permutation336 permutation14
    _ = injectiveMoment H node3210 := by rfl

def raw9691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw9691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw9691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical9691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9691 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw9691 = injectiveMoment H raw9691step0 := by
      have hz : ∀ j, raw9691 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9691step0 = (fun i j => raw9691 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9691 permutation151 hz
    injectiveMoment H raw9691step0 = injectiveMoment H raw9691step1 := by
      have heq : raw9691step1 = (fun i j => raw9691step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9691step0 permutation128 permutation3
    _ = injectiveMoment H node570 := by rfl

def raw9692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw9692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw9692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical9692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9692 = injectiveMoment H node440 := by
  calc
    injectiveMoment H raw9692 = injectiveMoment H raw9692step0 := by
      have hz : ∀ j, raw9692 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9692step0 = (fun i j => raw9692 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9692 permutation151 hz
    injectiveMoment H raw9692step0 = injectiveMoment H raw9692step1 := by
      have heq : raw9692step1 = (fun i j => raw9692step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9692step0 permutation128 permutation3
    _ = injectiveMoment H node440 := by rfl

def raw9693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw9693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw9693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical9693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9693 = injectiveMoment H node1139 := by
  calc
    injectiveMoment H raw9693 = injectiveMoment H raw9693step0 := by
      have hz : ∀ j, raw9693 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9693step0 = (fun i j => raw9693 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9693 permutation151 hz
    injectiveMoment H raw9693step0 = injectiveMoment H raw9693step1 := by
      have heq : raw9693step1 = (fun i j => raw9693step0 (permutation120 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9693step0 permutation120 permutation6
    _ = injectiveMoment H node1139 := by rfl

def raw9694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw9694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw9694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical9694 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9694 = injectiveMoment H node739 := by
  calc
    injectiveMoment H raw9694 = injectiveMoment H raw9694step0 := by
      have hz : ∀ j, raw9694 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9694step0 = (fun i j => raw9694 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9694 permutation151 hz
    injectiveMoment H raw9694step0 = injectiveMoment H raw9694step1 := by
      have heq : raw9694step1 = (fun i j => raw9694step0 (permutation143 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9694step0 permutation143 permutation5
    _ = injectiveMoment H node739 := by rfl

def raw9695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw9695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw9695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical9695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9695 = injectiveMoment H node441 := by
  calc
    injectiveMoment H raw9695 = injectiveMoment H raw9695step0 := by
      have hz : ∀ j, raw9695 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9695step0 = (fun i j => raw9695 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9695 permutation151 hz
    injectiveMoment H raw9695step0 = injectiveMoment H raw9695step1 := by
      have heq : raw9695step1 = (fun i j => raw9695step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9695step0 permutation128 permutation3
    _ = injectiveMoment H node441 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
