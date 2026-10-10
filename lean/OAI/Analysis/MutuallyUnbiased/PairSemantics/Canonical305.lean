import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9760 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 4, -3, 0], ![1, -4, 2, 1]]

def raw9760step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 4, -4], ![1, -3, 2], ![-1, 0, 1]]

def raw9760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -4, 4], ![-1, 3, -2], ![1, 0, -1]]

def raw9760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical9760 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9760 = injectiveMoment H node270 := by
  calc
    injectiveMoment H raw9760 = injectiveMoment H raw9760step0 := by
      have heq : raw9760step0 = raw9760.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9760).symm
    injectiveMoment H raw9760step0 = injectiveMoment H raw9760step1 := by
      have heq : raw9760step1 = -raw9760step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9760step0).symm
    injectiveMoment H raw9760step1 = injectiveMoment H raw9760step2 := by
      have heq : raw9760step2 = (fun i j => raw9760step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9760step1 permutation21 permutation4
    _ = injectiveMoment H node270 := by rfl

def raw9761 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 4, -2, -1], ![1, -4, 1, 2]]

def raw9761step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![-1, -1, 2]]

def raw9761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

theorem canonical9761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9761 = injectiveMoment H node286 := by
  calc
    injectiveMoment H raw9761 = injectiveMoment H raw9761step0 := by
      have heq : raw9761step0 = raw9761.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9761).symm
    injectiveMoment H raw9761step0 = injectiveMoment H raw9761step1 := by
      have heq : raw9761step1 = (fun i j => raw9761step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9761step0 permutation27 permutation3
    _ = injectiveMoment H node286 := by rfl

def raw9762 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw9762step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9762 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9762 = injectiveMoment H node3044 := by
  calc
    injectiveMoment H raw9762 = injectiveMoment H raw9762step0 := by
      have heq : raw9762step0 = (fun i j => raw9762 (permutation357 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9762 permutation357 permutation11
    _ = injectiveMoment H node3044 := by rfl

def raw9763 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9763step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9763 = injectiveMoment H node3339 := by
  calc
    injectiveMoment H raw9763 = injectiveMoment H raw9763step0 := by
      have heq : raw9763step0 = (fun i j => raw9763 (permutation334 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9763 permutation334 permutation15
    _ = injectiveMoment H node3339 := by rfl

def raw9764 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9764step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9764 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9764 = injectiveMoment H node1523 := by
  calc
    injectiveMoment H raw9764 = injectiveMoment H raw9764step0 := by
      have hz : ∀ j, raw9764 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9764step0 = (fun i j => raw9764 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9764 permutation202 hz
    injectiveMoment H raw9764step0 = injectiveMoment H raw9764step1 := by
      have heq : raw9764step1 = (fun i j => raw9764step0 (permutation149 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9764step0 permutation149 permutation23
    _ = injectiveMoment H node1523 := by rfl

def raw9765 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9765step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9765 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9765 = injectiveMoment H node1507 := by
  calc
    injectiveMoment H raw9765 = injectiveMoment H raw9765step0 := by
      have hz : ∀ j, raw9765 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9765step0 = (fun i j => raw9765 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9765 permutation202 hz
    injectiveMoment H raw9765step0 = injectiveMoment H raw9765step1 := by
      have heq : raw9765step1 = (fun i j => raw9765step0 (permutation139 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9765step0 permutation139 permutation11
    _ = injectiveMoment H node1507 := by rfl

def raw9766 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9766step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9766step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical9766 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9766 = injectiveMoment H node1680 := by
  calc
    injectiveMoment H raw9766 = injectiveMoment H raw9766step0 := by
      have hz : ∀ j, raw9766 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9766step0 = (fun i j => raw9766 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9766 permutation202 hz
    injectiveMoment H raw9766step0 = injectiveMoment H raw9766step1 := by
      have heq : raw9766step1 = (fun i j => raw9766step0 (permutation104 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9766step0 permutation104 permutation9
    _ = injectiveMoment H node1680 := by rfl

def raw9767 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9767step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9767step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical9767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9767 = injectiveMoment H node1631 := by
  calc
    injectiveMoment H raw9767 = injectiveMoment H raw9767step0 := by
      have hz : ∀ j, raw9767 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9767step0 = (fun i j => raw9767 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9767 permutation202 hz
    injectiveMoment H raw9767step0 = injectiveMoment H raw9767step1 := by
      have heq : raw9767step1 = (fun i j => raw9767step0 (permutation112 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9767step0 permutation112 permutation11
    _ = injectiveMoment H node1631 := by rfl

def raw9768 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9768step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9768step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9768step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical9768 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9768 = injectiveMoment H node2742 := by
  calc
    injectiveMoment H raw9768 = injectiveMoment H raw9768step0 := by
      have heq : raw9768step0 = -raw9768 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9768).symm
    injectiveMoment H raw9768step0 = injectiveMoment H raw9768step1 := by
      have hz : ∀ j, raw9768step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9768step1 = (fun i j => raw9768step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9768step0 permutation202 hz
    injectiveMoment H raw9768step1 = injectiveMoment H raw9768step2 := by
      have heq : raw9768step2 = (fun i j => raw9768step1 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9768step1 permutation48 permutation21
    _ = injectiveMoment H node2742 := by rfl

def raw9769 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9769step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9769step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9769step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical9769 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9769 = injectiveMoment H node2739 := by
  calc
    injectiveMoment H raw9769 = injectiveMoment H raw9769step0 := by
      have heq : raw9769step0 = -raw9769 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9769).symm
    injectiveMoment H raw9769step0 = injectiveMoment H raw9769step1 := by
      have hz : ∀ j, raw9769step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9769step1 = (fun i j => raw9769step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9769step0 permutation202 hz
    injectiveMoment H raw9769step1 = injectiveMoment H raw9769step2 := by
      have heq : raw9769step2 = (fun i j => raw9769step1 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9769step1 permutation48 permutation21
    _ = injectiveMoment H node2739 := by rfl

def raw9770 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9770step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9770step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9770step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical9770 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9770 = injectiveMoment H node2748 := by
  calc
    injectiveMoment H raw9770 = injectiveMoment H raw9770step0 := by
      have heq : raw9770step0 = -raw9770 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9770).symm
    injectiveMoment H raw9770step0 = injectiveMoment H raw9770step1 := by
      have hz : ∀ j, raw9770step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9770step1 = (fun i j => raw9770step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9770step0 permutation202 hz
    injectiveMoment H raw9770step1 = injectiveMoment H raw9770step2 := by
      have heq : raw9770step2 = (fun i j => raw9770step1 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9770step1 permutation48 permutation21
    _ = injectiveMoment H node2748 := by rfl

def raw9771 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9771step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9771step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9771 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9771 = injectiveMoment H node2453 := by
  calc
    injectiveMoment H raw9771 = injectiveMoment H raw9771step0 := by
      have hz : ∀ j, raw9771 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9771step0 = (fun i j => raw9771 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9771 permutation202 hz
    injectiveMoment H raw9771step0 = injectiveMoment H raw9771step1 := by
      have heq : raw9771step1 = (fun i j => raw9771step0 (permutation148 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9771step0 permutation148 permutation23
    _ = injectiveMoment H node2453 := by rfl

def raw9772 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9772step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9772step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical9772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9772 = injectiveMoment H node2421 := by
  calc
    injectiveMoment H raw9772 = injectiveMoment H raw9772step0 := by
      have hz : ∀ j, raw9772 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9772step0 = (fun i j => raw9772 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9772 permutation202 hz
    injectiveMoment H raw9772step0 = injectiveMoment H raw9772step1 := by
      have heq : raw9772step1 = (fun i j => raw9772step0 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9772step0 permutation136 permutation21
    _ = injectiveMoment H node2421 := by rfl

def raw9773 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9773step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9773step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9773 = injectiveMoment H node2676 := by
  calc
    injectiveMoment H raw9773 = injectiveMoment H raw9773step0 := by
      have hz : ∀ j, raw9773 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9773step0 = (fun i j => raw9773 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9773 permutation202 hz
    injectiveMoment H raw9773step0 = injectiveMoment H raw9773step1 := by
      have heq : raw9773step1 = (fun i j => raw9773step0 (permutation125 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9773step0 permutation125 permutation23
    _ = injectiveMoment H node2676 := by rfl

def raw9774 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9774step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9774step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9774step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical9774 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9774 = injectiveMoment H node2749 := by
  calc
    injectiveMoment H raw9774 = injectiveMoment H raw9774step0 := by
      have heq : raw9774step0 = -raw9774 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9774).symm
    injectiveMoment H raw9774step0 = injectiveMoment H raw9774step1 := by
      have hz : ∀ j, raw9774step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9774step1 = (fun i j => raw9774step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9774step0 permutation202 hz
    injectiveMoment H raw9774step1 = injectiveMoment H raw9774step2 := by
      have heq : raw9774step2 = (fun i j => raw9774step1 (permutation34 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9774step1 permutation34 permutation23
    _ = injectiveMoment H node2749 := by rfl

def raw9775 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9775step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9775step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9775 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw9775 = injectiveMoment H raw9775step0 := by
      have hz : ∀ j, raw9775 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9775step0 = (fun i j => raw9775 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9775 permutation202 hz
    injectiveMoment H raw9775step0 = injectiveMoment H raw9775step1 := by
      have heq : raw9775step1 = (fun i j => raw9775step0 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9775step0 permutation136 permutation21
    _ = injectiveMoment H node2448 := by rfl

def raw9776 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9776step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9776step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical9776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9776 = injectiveMoment H node2400 := by
  calc
    injectiveMoment H raw9776 = injectiveMoment H raw9776step0 := by
      have hz : ∀ j, raw9776 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9776step0 = (fun i j => raw9776 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9776 permutation202 hz
    injectiveMoment H raw9776step0 = injectiveMoment H raw9776step1 := by
      have heq : raw9776step1 = (fun i j => raw9776step0 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9776step0 permutation136 permutation21
    _ = injectiveMoment H node2400 := by rfl

def raw9777 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9777step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9777step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9777step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical9777 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9777 = injectiveMoment H node2747 := by
  calc
    injectiveMoment H raw9777 = injectiveMoment H raw9777step0 := by
      have heq : raw9777step0 = -raw9777 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9777).symm
    injectiveMoment H raw9777step0 = injectiveMoment H raw9777step1 := by
      have hz : ∀ j, raw9777step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9777step1 = (fun i j => raw9777step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9777step0 permutation202 hz
    injectiveMoment H raw9777step1 = injectiveMoment H raw9777step2 := by
      have heq : raw9777step2 = (fun i j => raw9777step1 (permutation46 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9777step1 permutation46 permutation23
    _ = injectiveMoment H node2747 := by rfl

def raw9778 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9778step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9778step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9778step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical9778 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9778 = injectiveMoment H node1739 := by
  calc
    injectiveMoment H raw9778 = injectiveMoment H raw9778step0 := by
      have heq : raw9778step0 = -raw9778 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9778).symm
    injectiveMoment H raw9778step0 = injectiveMoment H raw9778step1 := by
      have hz : ∀ j, raw9778step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9778step1 = (fun i j => raw9778step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9778step0 permutation202 hz
    injectiveMoment H raw9778step1 = injectiveMoment H raw9778step2 := by
      have heq : raw9778step2 = (fun i j => raw9778step1 (permutation130 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9778step1 permutation130 permutation17
    _ = injectiveMoment H node1739 := by rfl

def raw9779 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9779step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9779step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9779step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical9779 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9779 = injectiveMoment H node2740 := by
  calc
    injectiveMoment H raw9779 = injectiveMoment H raw9779step0 := by
      have heq : raw9779step0 = -raw9779 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9779).symm
    injectiveMoment H raw9779step0 = injectiveMoment H raw9779step1 := by
      have hz : ∀ j, raw9779step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9779step1 = (fun i j => raw9779step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9779step0 permutation202 hz
    injectiveMoment H raw9779step1 = injectiveMoment H raw9779step2 := by
      have heq : raw9779step2 = (fun i j => raw9779step1 (permutation46 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9779step1 permutation46 permutation23
    _ = injectiveMoment H node2740 := by rfl

def raw9780 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9780step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9780step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical9780 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9780 = injectiveMoment H node2532 := by
  calc
    injectiveMoment H raw9780 = injectiveMoment H raw9780step0 := by
      have hz : ∀ j, raw9780 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9780step0 = (fun i j => raw9780 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9780 permutation202 hz
    injectiveMoment H raw9780step0 = injectiveMoment H raw9780step1 := by
      have heq : raw9780step1 = (fun i j => raw9780step0 (permutation136 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9780step0 permutation136 permutation23
    _ = injectiveMoment H node2532 := by rfl

def raw9781 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9781step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9781step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9781step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical9781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9781 = injectiveMoment H node2750 := by
  calc
    injectiveMoment H raw9781 = injectiveMoment H raw9781step0 := by
      have heq : raw9781step0 = -raw9781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9781).symm
    injectiveMoment H raw9781step0 = injectiveMoment H raw9781step1 := by
      have hz : ∀ j, raw9781step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9781step1 = (fun i j => raw9781step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9781step0 permutation202 hz
    injectiveMoment H raw9781step1 = injectiveMoment H raw9781step2 := by
      have heq : raw9781step2 = (fun i j => raw9781step1 (permutation40 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9781step1 permutation40 permutation21
    _ = injectiveMoment H node2750 := by rfl

def raw9782 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9782step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9782step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9782 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9782 = injectiveMoment H node2402 := by
  calc
    injectiveMoment H raw9782 = injectiveMoment H raw9782step0 := by
      have hz : ∀ j, raw9782 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9782step0 = (fun i j => raw9782 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9782 permutation202 hz
    injectiveMoment H raw9782step0 = injectiveMoment H raw9782step1 := by
      have heq : raw9782step1 = (fun i j => raw9782step0 (permutation148 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9782step0 permutation148 permutation21
    _ = injectiveMoment H node2402 := by rfl

def raw9783 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9783step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical9783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9783 = injectiveMoment H node2836 := by
  calc
    injectiveMoment H raw9783 = injectiveMoment H raw9783step0 := by
      have heq : raw9783step0 = (fun i j => raw9783 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9783 permutation80 permutation9
    _ = injectiveMoment H node2836 := by rfl

def raw9784 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, -1, -1, 1]]

def raw9784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1], ![-1, -1, 1, 1]]

def raw9784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem canonical9784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9784 = injectiveMoment H node1114 := by
  calc
    injectiveMoment H raw9784 = injectiveMoment H raw9784step0 := by
      have heq : raw9784step0 = raw9784.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9784).symm
    injectiveMoment H raw9784step0 = injectiveMoment H raw9784step1 := by
      have heq : raw9784step1 = (fun i j => raw9784step0 (permutation27 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9784step0 permutation27 permutation9
    _ = injectiveMoment H node1114 := by rfl

def raw9785 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9785step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical9785 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9785 = injectiveMoment H node2823 := by
  calc
    injectiveMoment H raw9785 = injectiveMoment H raw9785step0 := by
      have heq : raw9785step0 = (fun i j => raw9785 (permutation92 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9785 permutation92 permutation11
    _ = injectiveMoment H node2823 := by rfl

def raw9786 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -2, -2, 3]]

def raw9786step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2], ![-1, -1, -1, 3]]

def raw9786step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical9786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9786 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw9786 = injectiveMoment H raw9786step0 := by
      have heq : raw9786step0 = raw9786.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9786).symm
    injectiveMoment H raw9786step0 = injectiveMoment H raw9786step1 := by
      have heq : raw9786step1 = (fun i j => raw9786step0 (permutation27 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9786step0 permutation27 permutation9
    _ = injectiveMoment H node959 := by rfl

def raw9787 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw9787step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical9787 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9787 = injectiveMoment H node3458 := by
  calc
    injectiveMoment H raw9787 = injectiveMoment H raw9787step0 := by
      have heq : raw9787step0 = (fun i j => raw9787 (permutation247 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9787 permutation247 permutation17
    _ = injectiveMoment H node3458 := by rfl

def raw9788 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9788step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9788step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9788 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9788 = injectiveMoment H node1523 := by
  calc
    injectiveMoment H raw9788 = injectiveMoment H raw9788step0 := by
      have hz : ∀ j, raw9788 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9788step0 = (fun i j => raw9788 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9788 permutation221 hz
    injectiveMoment H raw9788step0 = injectiveMoment H raw9788step1 := by
      have heq : raw9788step1 = (fun i j => raw9788step0 (permutation149 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9788step0 permutation149 permutation23
    _ = injectiveMoment H node1523 := by rfl

def raw9789 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9789step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9789step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9789 = injectiveMoment H node1507 := by
  calc
    injectiveMoment H raw9789 = injectiveMoment H raw9789step0 := by
      have hz : ∀ j, raw9789 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9789step0 = (fun i j => raw9789 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9789 permutation221 hz
    injectiveMoment H raw9789step0 = injectiveMoment H raw9789step1 := by
      have heq : raw9789step1 = (fun i j => raw9789step0 (permutation139 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9789step0 permutation139 permutation11
    _ = injectiveMoment H node1507 := by rfl

def raw9790 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9790step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

theorem canonical9790 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9790 = injectiveMoment H node3293 := by
  calc
    injectiveMoment H raw9790 = injectiveMoment H raw9790step0 := by
      have heq : raw9790step0 = (fun i j => raw9790 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9790 permutation258 permutation9
    _ = injectiveMoment H node3293 := by rfl

def raw9791 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9791step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem canonical9791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9791 = injectiveMoment H node3240 := by
  calc
    injectiveMoment H raw9791 = injectiveMoment H raw9791step0 := by
      have heq : raw9791step0 = (fun i j => raw9791 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9791 permutation308 permutation9
    _ = injectiveMoment H node3240 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
