import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5760 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5760step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 0, 0, -1], ![2, 0, -2, 0]]

def raw5760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0]]

def raw5760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5760 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5760 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw5760 = injectiveMoment H raw5760step0 := by
      have heq : raw5760step0 = raw5760.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5760).symm
    injectiveMoment H raw5760step0 = injectiveMoment H raw5760step1 := by
      have hz : ∀ i, raw5760step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5760step1 = (fun i j => raw5760step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5760step0 permutation15 hz
    injectiveMoment H raw5760step1 = injectiveMoment H raw5760step2 := by
      have heq : raw5760step2 = (fun i j => raw5760step1 (permutation26 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5760step1 permutation26 permutation8
    _ = injectiveMoment H node291 := by rfl

def raw5761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

theorem canonical5761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5761 = injectiveMoment H node2446 := by
  rfl

def raw5762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical5762 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5762 = injectiveMoment H node2447 := by
  rfl

def raw5763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical5763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5763 = injectiveMoment H node2448 := by
  rfl

def raw5764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical5764 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5764 = injectiveMoment H node2449 := by
  rfl

def raw5765 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw5765step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 1, -1, -1], ![2, -1, 0, -1]]

def raw5765step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, 0, -1, -1], ![-1, -1, 1, 1], ![-2, 1, 0, 1]]

def raw5765step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical5765 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5765 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw5765 = injectiveMoment H raw5765step0 := by
      have heq : raw5765step0 = raw5765.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5765).symm
    injectiveMoment H raw5765step0 = injectiveMoment H raw5765step1 := by
      have heq : raw5765step1 = -raw5765step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5765step0).symm
    injectiveMoment H raw5765step1 = injectiveMoment H raw5765step2 := by
      have heq : raw5765step2 = (fun i j => raw5765step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5765step1 permutation16 permutation24
    _ = injectiveMoment H node1260 := by rfl

def raw5766 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5766step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw5766step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical5766 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5766 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw5766 = injectiveMoment H raw5766step0 := by
      have heq : raw5766step0 = raw5766.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5766).symm
    injectiveMoment H raw5766step0 = injectiveMoment H raw5766step1 := by
      have heq : raw5766step1 = (fun i j => raw5766step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5766step0 permutation28 permutation24
    _ = injectiveMoment H node1047 := by rfl

def raw5767 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical5767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5767 = injectiveMoment H node839 := by
  rfl

def raw5768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw5768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 1, -2, 0], ![2, -1, 0, -1]]

def raw5768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical5768 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5768 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw5768 = injectiveMoment H raw5768step0 := by
      have heq : raw5768step0 = raw5768.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5768).symm
    injectiveMoment H raw5768step0 = injectiveMoment H raw5768step1 := by
      have heq : raw5768step1 = (fun i j => raw5768step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5768step0 permutation30 permutation30
    _ = injectiveMoment H node1053 := by rfl

def raw5769 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw5769step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 1, -1, -1], ![2, -1, -1, 0]]

def raw5769step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical5769 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5769 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw5769 = injectiveMoment H raw5769step0 := by
      have heq : raw5769step0 = raw5769.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5769).symm
    injectiveMoment H raw5769step0 = injectiveMoment H raw5769step1 := by
      have heq : raw5769step1 = (fun i j => raw5769step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5769step0 permutation29 permutation20
    _ = injectiveMoment H node1265 := by rfl

def raw5770 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5770 = injectiveMoment H node840 := by
  rfl

def raw5771 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical5771 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5771 = injectiveMoment H node842 := by
  rfl

def raw5772 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

theorem canonical5772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5772 = injectiveMoment H node843 := by
  rfl

def raw5773 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, -1, 0]]

def raw5773step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical5773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5773 = injectiveMoment H node854 := by
  calc
    injectiveMoment H raw5773 = injectiveMoment H raw5773step0 := by
      have heq : raw5773step0 = (fun i j => raw5773 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5773 permutation9 permutation10
    _ = injectiveMoment H node854 := by rfl

def raw5774 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![1, 2, -3, 0]]

def raw5774step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 2, -3], ![2, -2, 0]]

def raw5774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![-1, -2, 3], ![-2, 2, 0]]

def raw5774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical5774 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5774 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw5774 = injectiveMoment H raw5774step0 := by
      have heq : raw5774step0 = raw5774.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5774).symm
    injectiveMoment H raw5774step0 = injectiveMoment H raw5774step1 := by
      have heq : raw5774step1 = -raw5774step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5774step0).symm
    injectiveMoment H raw5774step1 = injectiveMoment H raw5774step2 := by
      have heq : raw5774step2 = (fun i j => raw5774step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5774step1 permutation21 permutation5
    _ = injectiveMoment H node177 := by rfl

def raw5775 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -3, 2], ![1, 1, 2, -4]]

def raw5775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2], ![2, 2, -4]]

def raw5775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical5775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5775 = injectiveMoment H node106 := by
  calc
    injectiveMoment H raw5775 = injectiveMoment H raw5775step0 := by
      have heq : raw5775step0 = raw5775.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5775).symm
    injectiveMoment H raw5775step0 = injectiveMoment H raw5775step1 := by
      have heq : raw5775step1 = (fun i j => raw5775step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5775step0 permutation21 permutation5
    _ = injectiveMoment H node106 := by rfl

def raw5776 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw5776step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -2, -1, 2], ![2, 1, 0, -3]]

def raw5776step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical5776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5776 = injectiveMoment H node836 := by
  calc
    injectiveMoment H raw5776 = injectiveMoment H raw5776step0 := by
      have heq : raw5776step0 = raw5776.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5776).symm
    injectiveMoment H raw5776step0 = injectiveMoment H raw5776step1 := by
      have heq : raw5776step1 = (fun i j => raw5776step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5776step0 permutation22 permutation23
    _ = injectiveMoment H node836 := by rfl

def raw5777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5777 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5777 = injectiveMoment H node845 := by
  rfl

def raw5778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5778 = injectiveMoment H node846 := by
  rfl

def raw5779 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical5779 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5779 = injectiveMoment H node847 := by
  rfl

def raw5780 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw5780step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 1, -3]]

def raw5780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical5780 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5780 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw5780 = injectiveMoment H raw5780step0 := by
      have heq : raw5780step0 = raw5780.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5780).symm
    injectiveMoment H raw5780step0 = injectiveMoment H raw5780step1 := by
      have heq : raw5780step1 = (fun i j => raw5780step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5780step0 permutation21 permutation5
    _ = injectiveMoment H node229 := by rfl

def raw5781 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw5781step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, -2, 2], ![2, 0, 1, -3]]

def raw5781step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical5781 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5781 = injectiveMoment H node836 := by
  calc
    injectiveMoment H raw5781 = injectiveMoment H raw5781step0 := by
      have heq : raw5781step0 = raw5781.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5781).symm
    injectiveMoment H raw5781step0 = injectiveMoment H raw5781step1 := by
      have heq : raw5781step1 = (fun i j => raw5781step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5781step0 permutation22 permutation17
    _ = injectiveMoment H node836 := by rfl

def raw5782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw5782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw5782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, -1, -1, 0], ![-1, 1, 1, -1], ![-2, 0, 0, 2]]

def raw5782step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical5782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5782 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw5782 = injectiveMoment H raw5782step0 := by
      have heq : raw5782step0 = raw5782.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5782).symm
    injectiveMoment H raw5782step0 = injectiveMoment H raw5782step1 := by
      have heq : raw5782step1 = -raw5782step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5782step0).symm
    injectiveMoment H raw5782step1 = injectiveMoment H raw5782step2 := by
      have heq : raw5782step2 = (fun i j => raw5782step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5782step1 permutation16 permutation18
    _ = injectiveMoment H node1040 := by rfl

def raw5783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5783step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw5783step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5783 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw5783 = injectiveMoment H raw5783step0 := by
      have heq : raw5783step0 = raw5783.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5783).symm
    injectiveMoment H raw5783step0 = injectiveMoment H raw5783step1 := by
      have heq : raw5783step1 = (fun i j => raw5783step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5783step0 permutation31 permutation26
    _ = injectiveMoment H node1044 := by rfl

def raw5784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw5784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, 1, -1], ![2, 0, -2, 0]]

def raw5784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5784 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw5784 = injectiveMoment H raw5784step0 := by
      have heq : raw5784step0 = raw5784.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5784).symm
    injectiveMoment H raw5784step0 = injectiveMoment H raw5784step1 := by
      have heq : raw5784step1 = (fun i j => raw5784step0 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5784step0 permutation25 permutation20
    _ = injectiveMoment H node1110 := by rfl

def raw5785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical5785 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5785 = injectiveMoment H node850 := by
  rfl

def raw5786 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw5786step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2]]

def raw5786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2]]

def raw5786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5786 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5786 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw5786 = injectiveMoment H raw5786step0 := by
      have heq : raw5786step0 = raw5786.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5786).symm
    injectiveMoment H raw5786step0 = injectiveMoment H raw5786step1 := by
      have heq : raw5786step1 = -raw5786step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5786step0).symm
    injectiveMoment H raw5786step1 = injectiveMoment H raw5786step2 := by
      have heq : raw5786step2 = (fun i j => raw5786step1 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5786step1 permutation16 permutation6
    _ = injectiveMoment H node284 := by rfl

def raw5787 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5787step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, 0, -1, 0], ![2, -1, 0, -1]]

def raw5787step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5787 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5787 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw5787 = injectiveMoment H raw5787step0 := by
      have heq : raw5787step0 = raw5787.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5787).symm
    injectiveMoment H raw5787step0 = injectiveMoment H raw5787step1 := by
      have heq : raw5787step1 = (fun i j => raw5787step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5787step0 permutation31 permutation20
    _ = injectiveMoment H node1044 := by rfl

def raw5788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5788step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, 0, 0, -1], ![2, -1, -1, 0]]

def raw5788step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical5788 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5788 = injectiveMoment H node1039 := by
  calc
    injectiveMoment H raw5788 = injectiveMoment H raw5788step0 := by
      have heq : raw5788step0 = raw5788.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5788).symm
    injectiveMoment H raw5788step0 = injectiveMoment H raw5788step1 := by
      have heq : raw5788step1 = (fun i j => raw5788step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5788step0 permutation31 permutation18
    _ = injectiveMoment H node1039 := by rfl

def raw5789 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw5789step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, 0, 1, -2], ![2, -1, -2, 1]]

def raw5789step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical5789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5789 = injectiveMoment H node838 := by
  calc
    injectiveMoment H raw5789 = injectiveMoment H raw5789step0 := by
      have heq : raw5789step0 = raw5789.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5789).symm
    injectiveMoment H raw5789step0 = injectiveMoment H raw5789step1 := by
      have heq : raw5789step1 = (fun i j => raw5789step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5789step0 permutation28 permutation18
    _ = injectiveMoment H node838 := by rfl

def raw5790 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5790step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1]]

def raw5790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5790 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5790 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw5790 = injectiveMoment H raw5790step0 := by
      have heq : raw5790step0 = raw5790.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5790).symm
    injectiveMoment H raw5790step0 = injectiveMoment H raw5790step1 := by
      have heq : raw5790step1 = (fun i j => raw5790step0 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5790step0 permutation31 permutation6
    _ = injectiveMoment H node283 := by rfl

def raw5791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw5791step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5791 = injectiveMoment H node846 := by
  calc
    injectiveMoment H raw5791 = injectiveMoment H raw5791step0 := by
      have heq : raw5791step0 = (fun i j => raw5791 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5791 permutation11 permutation9
    _ = injectiveMoment H node846 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
