import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5728 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 0, -2, 1], ![0, 2, 2, -4]]

def raw5728step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2], ![3, 1, -4]]

def raw5728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical5728 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5728 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw5728 = injectiveMoment H raw5728step0 := by
      have heq : raw5728step0 = raw5728.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5728).symm
    injectiveMoment H raw5728step0 = injectiveMoment H raw5728step1 := by
      have heq : raw5728step1 = (fun i j => raw5728step0 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5728step0 permutation23 permutation5
    _ = injectiveMoment H node201 := by rfl

def raw5729 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 0, 1, -2], ![0, 2, -1, -1]]

def raw5729step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![3, -2, -1]]

def raw5729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5729 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5729 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw5729 = injectiveMoment H raw5729step0 := by
      have heq : raw5729step0 = raw5729.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5729).symm
    injectiveMoment H raw5729step0 = injectiveMoment H raw5729step1 := by
      have heq : raw5729step1 = (fun i j => raw5729step0 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5729step0 permutation30 permutation6
    _ = injectiveMoment H node185 := by rfl

def raw5730 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 0, 2, -3], ![0, 2, -2, 0]]

def raw5730step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 2, -2], ![3, -3, 0]]

def raw5730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical5730 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5730 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw5730 = injectiveMoment H raw5730step0 := by
      have heq : raw5730step0 = raw5730.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5730).symm
    injectiveMoment H raw5730step0 = injectiveMoment H raw5730step1 := by
      have heq : raw5730step1 = (fun i j => raw5730step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5730step0 permutation22 permutation7
    _ = injectiveMoment H node204 := by rfl

def raw5731 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 1, -3, 1], ![0, 1, 3, -4]]

def raw5731step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3], ![3, 1, -4]]

def raw5731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, -1, -1], ![0, 3, -3], ![-3, -1, 4]]

def raw5731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical5731 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5731 = injectiveMoment H node87 := by
  calc
    injectiveMoment H raw5731 = injectiveMoment H raw5731step0 := by
      have heq : raw5731step0 = raw5731.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5731).symm
    injectiveMoment H raw5731step0 = injectiveMoment H raw5731step1 := by
      have heq : raw5731step1 = -raw5731step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5731step0).symm
    injectiveMoment H raw5731step1 = injectiveMoment H raw5731step2 := by
      have heq : raw5731step2 = (fun i j => raw5731step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5731step1 permutation31 permutation3
    _ = injectiveMoment H node87 := by rfl

def raw5732 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 1, -2, 0], ![0, 1, 2, -3]]

def raw5732step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![3, 0, -3]]

def raw5732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical5732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5732 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw5732 = injectiveMoment H raw5732step0 := by
      have heq : raw5732step0 = raw5732.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5732).symm
    injectiveMoment H raw5732step0 = injectiveMoment H raw5732step1 := by
      have heq : raw5732step1 = (fun i j => raw5732step0 (permutation26 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5732step0 permutation26 permutation5
    _ = injectiveMoment H node215 := by rfl

def raw5733 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical5733 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5733 = injectiveMoment H node2431 := by
  rfl

def raw5734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, -2, 0, 3]]

def raw5734step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

theorem canonical5734 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5734 = injectiveMoment H node796 := by
  calc
    injectiveMoment H raw5734 = injectiveMoment H raw5734step0 := by
      have heq : raw5734step0 = -raw5734 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5734).symm
    injectiveMoment H raw5734step0 = injectiveMoment H raw5734step1 := by
      have heq : raw5734step1 = (fun i j => raw5734step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5734step0 permutation32 permutation9
    _ = injectiveMoment H node796 := by rfl

def raw5735 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

theorem canonical5735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5735 = injectiveMoment H node826 := by
  rfl

def raw5736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

theorem canonical5736 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5736 = injectiveMoment H node827 := by
  rfl

def raw5737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical5737 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5737 = injectiveMoment H node828 := by
  rfl

def raw5738 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical5738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5738 = injectiveMoment H node831 := by
  rfl

def raw5739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical5739 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5739 = injectiveMoment H node832 := by
  rfl

def raw5740 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical5740 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5740 = injectiveMoment H node833 := by
  rfl

def raw5741 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![1, 2, 1, -4]]

def raw5741step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 2, -4]]

def raw5741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![-1, 2, -1], ![-2, -2, 4]]

def raw5741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5741 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw5741 = injectiveMoment H raw5741step0 := by
      have heq : raw5741step0 = raw5741.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5741).symm
    injectiveMoment H raw5741step0 = injectiveMoment H raw5741step1 := by
      have heq : raw5741step1 = -raw5741step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5741step0).symm
    injectiveMoment H raw5741step1 = injectiveMoment H raw5741step2 := by
      have heq : raw5741step2 = (fun i j => raw5741step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5741step1 permutation27 permutation5
    _ = injectiveMoment H node146 := by rfl

def raw5742 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical5742 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5742 = injectiveMoment H node2436 := by
  rfl

def raw5743 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical5743 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5743 = injectiveMoment H node2437 := by
  rfl

def raw5744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5744step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw5744step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw5744step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical5744 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5744 = injectiveMoment H node1284 := by
  calc
    injectiveMoment H raw5744 = injectiveMoment H raw5744step0 := by
      have heq : raw5744step0 = -raw5744 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5744).symm
    injectiveMoment H raw5744step0 = injectiveMoment H raw5744step1 := by
      have hz : ∀ j, raw5744step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5744step1 = (fun i j => raw5744step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5744step0 permutation80 hz
    injectiveMoment H raw5744step1 = injectiveMoment H raw5744step2 := by
      have heq : raw5744step2 = (fun i j => raw5744step1 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5744step1 permutation32 permutation11
    _ = injectiveMoment H node1284 := by rfl

def raw5745 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical5745 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5745 = injectiveMoment H node2439 := by
  rfl

def raw5746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical5746 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5746 = injectiveMoment H node2440 := by
  rfl

def raw5747 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

theorem canonical5747 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5747 = injectiveMoment H node834 := by
  rfl

def raw5748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical5748 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5748 = injectiveMoment H node2441 := by
  rfl

def raw5749 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5749 = injectiveMoment H node2443 := by
  rfl

def raw5750 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical5750 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5750 = injectiveMoment H node2444 := by
  rfl

def raw5751 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw5751step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, 1, 0, -3]]

def raw5751step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical5751 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5751 = injectiveMoment H node1116 := by
  calc
    injectiveMoment H raw5751 = injectiveMoment H raw5751step0 := by
      have heq : raw5751step0 = raw5751.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5751).symm
    injectiveMoment H raw5751step0 = injectiveMoment H raw5751step1 := by
      have heq : raw5751step1 = (fun i j => raw5751step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5751step0 permutation21 permutation17
    _ = injectiveMoment H node1116 := by rfl

def raw5752 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw5752step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, -1, 0, 2]]

def raw5752step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical5752 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5752 = injectiveMoment H node1259 := by
  calc
    injectiveMoment H raw5752 = injectiveMoment H raw5752step0 := by
      have heq : raw5752step0 = -raw5752 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5752).symm
    injectiveMoment H raw5752step0 = injectiveMoment H raw5752step1 := by
      have heq : raw5752step1 = (fun i j => raw5752step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5752step0 permutation32 permutation11
    _ = injectiveMoment H node1259 := by rfl

def raw5753 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical5753 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5753 = injectiveMoment H node837 := by
  rfl

def raw5754 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5754step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw5754step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical5754 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5754 = injectiveMoment H node1284 := by
  calc
    injectiveMoment H raw5754 = injectiveMoment H raw5754step0 := by
      have heq : raw5754step0 = -raw5754 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5754).symm
    injectiveMoment H raw5754step0 = injectiveMoment H raw5754step1 := by
      have heq : raw5754step1 = (fun i j => raw5754step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5754step0 permutation32 permutation11
    _ = injectiveMoment H node1284 := by rfl

def raw5755 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5755step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, -1, 1, -1], ![2, 1, -3, 0]]

def raw5755step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical5755 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5755 = injectiveMoment H node1109 := by
  calc
    injectiveMoment H raw5755 = injectiveMoment H raw5755step0 := by
      have heq : raw5755step0 = raw5755.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5755).symm
    injectiveMoment H raw5755step0 = injectiveMoment H raw5755step1 := by
      have heq : raw5755step1 = (fun i j => raw5755step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5755step0 permutation23 permutation19
    _ = injectiveMoment H node1109 := by rfl

def raw5756 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw5756step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, -1, 2, -2], ![2, 1, -4, 1]]

def raw5756step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

theorem canonical5756 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5756 = injectiveMoment H node826 := by
  calc
    injectiveMoment H raw5756 = injectiveMoment H raw5756step0 := by
      have heq : raw5756step0 = raw5756.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5756).symm
    injectiveMoment H raw5756step0 = injectiveMoment H raw5756step1 := by
      have heq : raw5756step1 = (fun i j => raw5756step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5756step0 permutation23 permutation19
    _ = injectiveMoment H node826 := by rfl

def raw5757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5757step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-1, 0, 0, 0, 1], ![-2, 0, 1, 1, 0], ![1, 0, -1, 0, 0], ![2, 0, 0, -1, -1]]

def raw5757step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw5757step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5757 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5757 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw5757 = injectiveMoment H raw5757step0 := by
      have heq : raw5757step0 = raw5757.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5757).symm
    injectiveMoment H raw5757step0 = injectiveMoment H raw5757step1 := by
      have hz : ∀ i, raw5757step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw5757step1 = (fun i j => raw5757step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5757step0 permutation57 hz
    injectiveMoment H raw5757step1 = injectiveMoment H raw5757step2 := by
      have heq : raw5757step2 = (fun i j => raw5757step1 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5757step1 permutation31 permutation26
    _ = injectiveMoment H node1044 := by rfl

def raw5758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5758step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 0, 0, -1], ![2, 0, -1, -1]]

def raw5758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1]]

def raw5758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5758 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5758 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw5758 = injectiveMoment H raw5758step0 := by
      have heq : raw5758step0 = raw5758.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5758).symm
    injectiveMoment H raw5758step0 = injectiveMoment H raw5758step1 := by
      have hz : ∀ i, raw5758step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5758step1 = (fun i j => raw5758step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5758step0 permutation15 hz
    injectiveMoment H raw5758step1 = injectiveMoment H raw5758step2 := by
      have heq : raw5758step2 = (fun i j => raw5758step1 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5758step1 permutation31 permutation6
    _ = injectiveMoment H node283 := by rfl

def raw5759 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 0, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5759step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 0, -1, 0], ![2, 0, -1, -1]]

def raw5759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1]]

def raw5759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5759 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5759 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw5759 = injectiveMoment H raw5759step0 := by
      have heq : raw5759step0 = raw5759.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5759).symm
    injectiveMoment H raw5759step0 = injectiveMoment H raw5759step1 := by
      have hz : ∀ i, raw5759step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5759step1 = (fun i j => raw5759step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5759step0 permutation15 hz
    injectiveMoment H raw5759step1 = injectiveMoment H raw5759step2 := by
      have heq : raw5759step2 = (fun i j => raw5759step1 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5759step1 permutation32 permutation8
    _ = injectiveMoment H node284 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
