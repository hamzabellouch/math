import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]

def raw2752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical2752 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2752 = injectiveMoment H node556 := by
  calc
    injectiveMoment H raw2752 = injectiveMoment H raw2752step0 := by
      have heq : raw2752step0 = (fun i j => raw2752 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2752 permutation35 permutation3
    _ = injectiveMoment H node556 := by rfl

def raw2753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2753 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2753 = injectiveMoment H node561 := by
  rfl

def raw2754 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical2754 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2754 = injectiveMoment H node562 := by
  rfl

def raw2755 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]

def raw2755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2755 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2755 = injectiveMoment H node561 := by
  calc
    injectiveMoment H raw2755 = injectiveMoment H raw2755step0 := by
      have heq : raw2755step0 = (fun i j => raw2755 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2755 permutation34 permutation3
    _ = injectiveMoment H node561 := by rfl

def raw2756 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical2756 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2756 = injectiveMoment H node169 := by
  rfl

def raw2757 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2757 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2757 = injectiveMoment H node563 := by
  rfl

def raw2758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]

def raw2758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2758 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2758 = injectiveMoment H node563 := by
  calc
    injectiveMoment H raw2758 = injectiveMoment H raw2758step0 := by
      have heq : raw2758step0 = (fun i j => raw2758 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2758 permutation34 permutation3
    _ = injectiveMoment H node563 := by rfl

def raw2759 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical2759 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2759 = injectiveMoment H node170 := by
  rfl

def raw2760 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

theorem canonical2760 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2760 = injectiveMoment H node564 := by
  rfl

def raw2761 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical2761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2761 = injectiveMoment H node565 := by
  rfl

def raw2762 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -2, 1], ![1, 4, -5]]

theorem canonical2762 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2762 = injectiveMoment H node172 := by
  rfl

def raw2763 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 2, -3]]

def raw2763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2763 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw2763 = injectiveMoment H raw2763step0 := by
      have heq : raw2763step0 = (fun i j => raw2763 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2763 permutation35 permutation3
    _ = injectiveMoment H node559 := by rfl

def raw2764 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw2764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2764 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2764 = injectiveMoment H node563 := by
  calc
    injectiveMoment H raw2764 = injectiveMoment H raw2764step0 := by
      have heq : raw2764step0 = (fun i j => raw2764 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2764 permutation37 permutation3
    _ = injectiveMoment H node563 := by rfl

def raw2765 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical2765 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2765 = injectiveMoment H node173 := by
  rfl

def raw2766 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical2766 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2766 = injectiveMoment H node174 := by
  rfl

def raw2767 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical2767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2767 = injectiveMoment H node175 := by
  rfl

def raw2768 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]

def raw2768step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical2768 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2768 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw2768 = injectiveMoment H raw2768step0 := by
      have heq : raw2768step0 = (fun i j => raw2768 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2768 permutation10 permutation3
    _ = injectiveMoment H node174 := by rfl

def raw2769 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw2769step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical2769 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2769 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw2769 = injectiveMoment H raw2769step0 := by
      have hz : ∀ j, raw2769 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw2769step0 = (fun i j => raw2769 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2769 permutation57 hz
    _ = injectiveMoment H node176 := by rfl

def raw2770 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw2770step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical2770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2770 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw2770 = injectiveMoment H raw2770step0 := by
      have hz : ∀ j, raw2770 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw2770step0 = (fun i j => raw2770 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2770 permutation57 hz
    _ = injectiveMoment H node177 := by rfl

def raw2771 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw2771step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical2771 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2771 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw2771 = injectiveMoment H raw2771step0 := by
      have hz : ∀ j, raw2771 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw2771step0 = (fun i j => raw2771 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2771 permutation57 hz
    _ = injectiveMoment H node180 := by rfl

def raw2772 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw2772step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2772 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw2772 = injectiveMoment H raw2772step0 := by
      have hz : ∀ j, raw2772 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw2772step0 = (fun i j => raw2772 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2772 permutation57 hz
    _ = injectiveMoment H node181 := by rfl

def raw2773 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw2773step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw2773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical2773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2773 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw2773 = injectiveMoment H raw2773step0 := by
      have hz : ∀ j, raw2773 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw2773step0 = (fun i j => raw2773 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2773 permutation57 hz
    injectiveMoment H raw2773step0 = injectiveMoment H raw2773step1 := by
      have heq : raw2773step1 = (fun i j => raw2773step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2773step0 permutation12 permutation5
    _ = injectiveMoment H node271 := by rfl

def raw2774 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2]]

def raw2774step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]

def raw2774step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical2774 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2774 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2774 = injectiveMoment H raw2774step0 := by
      have hz : ∀ j, raw2774 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw2774step0 = (fun i j => raw2774 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2774 permutation15 hz
    injectiveMoment H raw2774step0 = injectiveMoment H raw2774step1 := by
      have heq : raw2774step1 = (fun i j => raw2774step0 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2774step0 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

def raw2775 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw2775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2775 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw2775 = injectiveMoment H raw2775step0 := by
      have hz : ∀ j, raw2775 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw2775step0 = (fun i j => raw2775 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2775 permutation57 hz
    _ = injectiveMoment H node185 := by rfl

def raw2776 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]

def raw2776step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical2776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2776 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw2776 = injectiveMoment H raw2776step0 := by
      have hz : ∀ j, raw2776 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw2776step0 = (fun i j => raw2776 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2776 permutation15 hz
    _ = injectiveMoment H node36 := by rfl

def raw2777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw2777step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical2777 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2777 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw2777 = injectiveMoment H raw2777step0 := by
      have hz : ∀ j, raw2777 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw2777step0 = (fun i j => raw2777 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2777 permutation57 hz
    _ = injectiveMoment H node187 := by rfl

def raw2778 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw2778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical2778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2778 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw2778 = injectiveMoment H raw2778step0 := by
      have hz : ∀ j, raw2778 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw2778step0 = (fun i j => raw2778 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2778 permutation57 hz
    _ = injectiveMoment H node188 := by rfl

def raw2779 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]

def raw2779step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical2779 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2779 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw2779 = injectiveMoment H raw2779step0 := by
      have hz : ∀ j, raw2779 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw2779step0 = (fun i j => raw2779 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2779 permutation15 hz
    _ = injectiveMoment H node37 := by rfl

def raw2780 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 3, -4]]

def raw2780step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical2780 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2780 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw2780 = injectiveMoment H raw2780step0 := by
      have hz : ∀ j, raw2780 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw2780step0 = (fun i j => raw2780 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2780 permutation15 hz
    _ = injectiveMoment H node40 := by rfl

def raw2781 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3]]

def raw2781step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![3, 0, 0, -3]]

def raw2781step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw2781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical2781 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2781 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2781 = injectiveMoment H raw2781step0 := by
      have heq : raw2781step0 = raw2781.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2781).symm
    injectiveMoment H raw2781step0 = injectiveMoment H raw2781step1 := by
      have hz : ∀ i, raw2781step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw2781step1 = (fun i j => raw2781step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2781step0 permutation15 hz
    injectiveMoment H raw2781step1 = injectiveMoment H raw2781step2 := by
      have heq : raw2781step2 = (fun i j => raw2781step1 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2781step1 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

def raw2782 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw2782step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]

def raw2782step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical2782 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2782 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2782 = injectiveMoment H raw2782step0 := by
      have hz : ∀ j, raw2782 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw2782step0 = (fun i j => raw2782 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2782 permutation15 hz
    injectiveMoment H raw2782step0 = injectiveMoment H raw2782step1 := by
      have heq : raw2782step1 = (fun i j => raw2782step0 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2782step0 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

def raw2783 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![2, 1, -3]]

def raw2783step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]

def raw2783step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw2783step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical2783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2783 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw2783 = injectiveMoment H raw2783step0 := by
      have heq : raw2783step0 = raw2783.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2783).symm
    injectiveMoment H raw2783step0 = injectiveMoment H raw2783step1 := by
      have hz : ∀ i, raw2783step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw2783step1 = (fun i j => raw2783step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2783step0 permutation5 hz
    injectiveMoment H raw2783step1 = injectiveMoment H raw2783step2 := by
      have heq : raw2783step2 = (fun i j => raw2783step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2783step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
