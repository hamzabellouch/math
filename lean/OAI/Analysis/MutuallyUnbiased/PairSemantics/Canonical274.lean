import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, -1, -1], ![-2, -1, 3]]

def raw8768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical8768 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8768 = injectiveMoment H node1866 := by
  calc
    injectiveMoment H raw8768 = injectiveMoment H raw8768step0 := by
      have heq : raw8768step0 = (fun i j => raw8768 (permutation373 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8768 permutation373 permutation3
    _ = injectiveMoment H node1866 := by rfl

def raw8769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw8769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical8769 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8769 = injectiveMoment H node1527 := by
  calc
    injectiveMoment H raw8769 = injectiveMoment H raw8769step0 := by
      have heq : raw8769step0 = (fun i j => raw8769 (permutation318 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8769 permutation318 permutation5
    _ = injectiveMoment H node1527 := by rfl

def raw8770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![-2, 3, -1], ![1, -3, 2]]

def raw8770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8770 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw8770 = injectiveMoment H raw8770step0 := by
      have hz : ∀ j, raw8770 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8770step0 = (fun i j => raw8770 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8770 permutation241 hz
    injectiveMoment H raw8770step0 = injectiveMoment H raw8770step1 := by
      have heq : raw8770step1 = (fun i j => raw8770step0 (permutation110 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8770step0 permutation110 permutation4
    _ = injectiveMoment H node559 := by rfl

def raw8771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![-1, 3, -2], ![0, -3, 3]]

def raw8771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical8771 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8771 = injectiveMoment H node883 := by
  calc
    injectiveMoment H raw8771 = injectiveMoment H raw8771step0 := by
      have hz : ∀ j, raw8771 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8771step0 = (fun i j => raw8771 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8771 permutation241 hz
    injectiveMoment H raw8771step0 = injectiveMoment H raw8771step1 := by
      have heq : raw8771step1 = (fun i j => raw8771step0 (permutation111 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8771step0 permutation111 permutation4
    _ = injectiveMoment H node883 := by rfl

def raw8772 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-1, -2, 3], ![-1, 3, -2]]

def raw8772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8772 = injectiveMoment H node2474 := by
  calc
    injectiveMoment H raw8772 = injectiveMoment H raw8772step0 := by
      have heq : raw8772step0 = (fun i j => raw8772 (permutation295 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8772 permutation295 permutation3
    _ = injectiveMoment H node2474 := by rfl

def raw8773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0], ![1, -3, 2]]

def raw8773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8773 = injectiveMoment H node1405 := by
  calc
    injectiveMoment H raw8773 = injectiveMoment H raw8773step0 := by
      have heq : raw8773step0 = (fun i j => raw8773 (permutation277 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8773 permutation277 permutation4
    _ = injectiveMoment H node1405 := by rfl

def raw8774 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![0, -3, 3]]

def raw8774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8774 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8774 = injectiveMoment H node1887 := by
  calc
    injectiveMoment H raw8774 = injectiveMoment H raw8774step0 := by
      have heq : raw8774step0 = (fun i j => raw8774 (permutation279 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8774 permutation279 permutation4
    _ = injectiveMoment H node1887 := by rfl

def raw8775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -3, 4], ![-1, 3, -2]]

def raw8775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8775 = injectiveMoment H node2383 := by
  calc
    injectiveMoment H raw8775 = injectiveMoment H raw8775step0 := by
      have heq : raw8775step0 = (fun i j => raw8775 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8775 permutation294 permutation3
    _ = injectiveMoment H node2383 := by rfl

def raw8776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 2, -1]]

def raw8776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8776 = injectiveMoment H node2471 := by
  calc
    injectiveMoment H raw8776 = injectiveMoment H raw8776step0 := by
      have heq : raw8776step0 = (fun i j => raw8776 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8776 permutation294 permutation3
    _ = injectiveMoment H node2471 := by rfl

def raw8777 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![-1, -3, 4]]

def raw8777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8777 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8777 = injectiveMoment H node2383 := by
  calc
    injectiveMoment H raw8777 = injectiveMoment H raw8777step0 := by
      have heq : raw8777step0 = (fun i j => raw8777 (permutation395 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8777 permutation395 permutation3
    _ = injectiveMoment H node2383 := by rfl

def raw8778 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![0, -1, 1]]

def raw8778step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw8778step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical8778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8778 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8778 = injectiveMoment H raw8778step0 := by
      have hz : ∀ i, raw8778 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8778step0 = (fun i j => raw8778 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8778 permutation3 hz
    injectiveMoment H raw8778step0 = injectiveMoment H raw8778step1 := by
      have heq : raw8778step1 = (fun i j => raw8778step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8778step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw8779 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def raw8779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def raw8779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8779 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8779 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw8779 = injectiveMoment H raw8779step0 := by
      have heq : raw8779step0 = -raw8779 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8779).symm
    injectiveMoment H raw8779step0 = injectiveMoment H raw8779step1 := by
      have heq : raw8779step1 = (fun i j => raw8779step0 (permutation60 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8779step0 permutation60 permutation4
    _ = injectiveMoment H node1151 := by rfl

def raw8780 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]

def raw8780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def raw8780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8780 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8780 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw8780 = injectiveMoment H raw8780step0 := by
      have heq : raw8780step0 = -raw8780 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8780).symm
    injectiveMoment H raw8780step0 = injectiveMoment H raw8780step1 := by
      have heq : raw8780step1 = (fun i j => raw8780step0 (permutation57 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8780step0 permutation57 permutation4
    _ = injectiveMoment H node1151 := by rfl

def raw8781 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def raw8781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8781 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8781 = injectiveMoment H node2108 := by
  calc
    injectiveMoment H raw8781 = injectiveMoment H raw8781step0 := by
      have heq : raw8781step0 = (fun i j => raw8781 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8781 permutation294 permutation3
    _ = injectiveMoment H node2108 := by rfl

def raw8782 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def raw8782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1]]

def raw8782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical8782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8782 = injectiveMoment H node2295 := by
  calc
    injectiveMoment H raw8782 = injectiveMoment H raw8782step0 := by
      have heq : raw8782step0 = -raw8782 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8782).symm
    injectiveMoment H raw8782step0 = injectiveMoment H raw8782step1 := by
      have heq : raw8782step1 = (fun i j => raw8782step0 (permutation404 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8782step0 permutation404 permutation6
    _ = injectiveMoment H node2295 := by rfl

def raw8783 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def raw8783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8783 = injectiveMoment H node1533 := by
  calc
    injectiveMoment H raw8783 = injectiveMoment H raw8783step0 := by
      have heq : raw8783step0 = (fun i j => raw8783 (permutation397 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8783 permutation397 permutation4
    _ = injectiveMoment H node1533 := by rfl

def raw8784 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def raw8784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8784 = injectiveMoment H node2108 := by
  calc
    injectiveMoment H raw8784 = injectiveMoment H raw8784step0 := by
      have heq : raw8784step0 = (fun i j => raw8784 (permutation296 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8784 permutation296 permutation3
    _ = injectiveMoment H node2108 := by rfl

def raw8785 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, 4, -3]]

def raw8785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

theorem canonical8785 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8785 = injectiveMoment H node1388 := by
  calc
    injectiveMoment H raw8785 = injectiveMoment H raw8785step0 := by
      have heq : raw8785step0 = (fun i j => raw8785 (permutation339 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8785 permutation339 permutation7
    _ = injectiveMoment H node1388 := by rfl

def raw8786 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![-1, 4, -3]]

def raw8786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8786 = injectiveMoment H node1869 := by
  calc
    injectiveMoment H raw8786 = injectiveMoment H raw8786step0 := by
      have heq : raw8786step0 = (fun i j => raw8786 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8786 permutation294 permutation3
    _ = injectiveMoment H node1869 := by rfl

def raw8787 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 3, -2]]

def raw8787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![1, -3, 2]]

def raw8787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8787 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8787 = injectiveMoment H node1432 := by
  calc
    injectiveMoment H raw8787 = injectiveMoment H raw8787step0 := by
      have heq : raw8787step0 = -raw8787 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8787).symm
    injectiveMoment H raw8787step0 = injectiveMoment H raw8787step1 := by
      have heq : raw8787step1 = (fun i j => raw8787step0 (permutation392 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8787step0 permutation392 permutation5
    _ = injectiveMoment H node1432 := by rfl

def raw8788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def raw8788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8788 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8788 = injectiveMoment H node2667 := by
  calc
    injectiveMoment H raw8788 = injectiveMoment H raw8788step0 := by
      have heq : raw8788step0 = (fun i j => raw8788 (permutation380 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8788 permutation380 permutation7
    _ = injectiveMoment H node2667 := by rfl

def raw8789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def raw8789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical8789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8789 = injectiveMoment H node1530 := by
  calc
    injectiveMoment H raw8789 = injectiveMoment H raw8789step0 := by
      have heq : raw8789step0 = (fun i j => raw8789 (permutation379 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8789 permutation379 permutation7
    _ = injectiveMoment H node1530 := by rfl

def raw8790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 2, -1]]

def raw8790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8790 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8790 = injectiveMoment H node2667 := by
  calc
    injectiveMoment H raw8790 = injectiveMoment H raw8790step0 := by
      have heq : raw8790step0 = (fun i j => raw8790 (permutation360 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8790 permutation360 permutation7
    _ = injectiveMoment H node2667 := by rfl

def raw8791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 4, -2]]

def raw8791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical8791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8791 = injectiveMoment H node1530 := by
  calc
    injectiveMoment H raw8791 = injectiveMoment H raw8791step0 := by
      have heq : raw8791step0 = (fun i j => raw8791 (permutation359 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8791 permutation359 permutation7
    _ = injectiveMoment H node1530 := by rfl

def raw8792 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1]]

def raw8792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1]]

def raw8792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8792 = injectiveMoment H node2301 := by
  calc
    injectiveMoment H raw8792 = injectiveMoment H raw8792step0 := by
      have heq : raw8792step0 = -raw8792 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8792).symm
    injectiveMoment H raw8792step0 = injectiveMoment H raw8792step1 := by
      have heq : raw8792step1 = (fun i j => raw8792step0 (permutation404 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8792step0 permutation404 permutation6
    _ = injectiveMoment H node2301 := by rfl

def raw8793 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 1, 0]]

def raw8793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0]]

def raw8793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8793 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8793 = injectiveMoment H node2660 := by
  calc
    injectiveMoment H raw8793 = injectiveMoment H raw8793step0 := by
      have heq : raw8793step0 = -raw8793 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8793).symm
    injectiveMoment H raw8793step0 = injectiveMoment H raw8793step1 := by
      have heq : raw8793step1 = (fun i j => raw8793step0 (permutation302 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8793step0 permutation302 permutation6
    _ = injectiveMoment H node2660 := by rfl

def raw8794 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-2, 4, -2]]

def raw8794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8794 = injectiveMoment H node1535 := by
  calc
    injectiveMoment H raw8794 = injectiveMoment H raw8794step0 := by
      have heq : raw8794step0 = (fun i j => raw8794 (permutation397 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8794 permutation397 permutation4
    _ = injectiveMoment H node1535 := by rfl

def raw8795 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 3, -1]]

def raw8795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]

def raw8795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8795 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8795 = injectiveMoment H node1434 := by
  calc
    injectiveMoment H raw8795 = injectiveMoment H raw8795step0 := by
      have heq : raw8795step0 = -raw8795 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8795).symm
    injectiveMoment H raw8795step0 = injectiveMoment H raw8795step1 := by
      have heq : raw8795step1 = (fun i j => raw8795step0 (permutation366 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8795step0 permutation366 permutation6
    _ = injectiveMoment H node1434 := by rfl

def raw8796 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-5, 2, 1, 2], ![5, -1, -2, -2]]

def raw8796step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -5, 5], ![-1, 2, -1], ![1, 1, -2], ![0, 2, -2]]

def raw8796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

theorem canonical8796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8796 = injectiveMoment H node282 := by
  calc
    injectiveMoment H raw8796 = injectiveMoment H raw8796step0 := by
      have heq : raw8796step0 = raw8796.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8796).symm
    injectiveMoment H raw8796step0 = injectiveMoment H raw8796step1 := by
      have heq : raw8796step1 = (fun i j => raw8796step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8796step0 permutation19 permutation4
    _ = injectiveMoment H node282 := by rfl

def raw8797 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-4, 2, 1, 1], ![4, -1, -2, -1]]

def raw8797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![1, 1, -2], ![0, 1, -1]]

def raw8797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

theorem canonical8797 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8797 = injectiveMoment H node286 := by
  calc
    injectiveMoment H raw8797 = injectiveMoment H raw8797step0 := by
      have heq : raw8797step0 = raw8797.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8797).symm
    injectiveMoment H raw8797step0 = injectiveMoment H raw8797step1 := by
      have heq : raw8797step1 = (fun i j => raw8797step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8797step0 permutation19 permutation4
    _ = injectiveMoment H node286 := by rfl

def raw8798 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, -1, 1, 3], ![3, 2, -2, -3]]

def raw8798step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![1, 1, -2], ![0, 3, -3]]

def raw8798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

theorem canonical8798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8798 = injectiveMoment H node277 := by
  calc
    injectiveMoment H raw8798 = injectiveMoment H raw8798step0 := by
      have heq : raw8798step0 = raw8798.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8798).symm
    injectiveMoment H raw8798step0 = injectiveMoment H raw8798step1 := by
      have heq : raw8798step1 = (fun i j => raw8798step0 (permutation16 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8798step0 permutation16 permutation3
    _ = injectiveMoment H node277 := by rfl

def raw8799 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, 2, -2, 3], ![3, -1, 1, -3]]

def raw8799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![1, -2, 1], ![0, 3, -3]]

def raw8799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

theorem canonical8799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8799 = injectiveMoment H node277 := by
  calc
    injectiveMoment H raw8799 = injectiveMoment H raw8799step0 := by
      have heq : raw8799step0 = raw8799.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8799).symm
    injectiveMoment H raw8799step0 = injectiveMoment H raw8799step1 := by
      have heq : raw8799step1 = (fun i j => raw8799step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8799step0 permutation19 permutation4
    _ = injectiveMoment H node277 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
