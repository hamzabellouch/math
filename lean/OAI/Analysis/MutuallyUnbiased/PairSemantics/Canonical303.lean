import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw9696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw9696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical9696 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9696 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw9696 = injectiveMoment H raw9696step0 := by
      have hz : ∀ j, raw9696 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9696step0 = (fun i j => raw9696 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9696 permutation151 hz
    injectiveMoment H raw9696step0 = injectiveMoment H raw9696step1 := by
      have heq : raw9696step1 = (fun i j => raw9696step0 (permutation120 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9696step0 permutation120 permutation6
    _ = injectiveMoment H node663 := by rfl

def raw9697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw9697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw9697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical9697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9697 = injectiveMoment H node737 := by
  calc
    injectiveMoment H raw9697 = injectiveMoment H raw9697step0 := by
      have hz : ∀ j, raw9697 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9697step0 = (fun i j => raw9697 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9697 permutation151 hz
    injectiveMoment H raw9697step0 = injectiveMoment H raw9697step1 := by
      have heq : raw9697step1 = (fun i j => raw9697step0 (permutation135 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9697step0 permutation135 permutation5
    _ = injectiveMoment H node737 := by rfl

def raw9698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def raw9698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]

def raw9698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]

def raw9698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical9698 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9698 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw9698 = injectiveMoment H raw9698step0 := by
      have heq : raw9698step0 = -raw9698 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9698).symm
    injectiveMoment H raw9698step0 = injectiveMoment H raw9698step1 := by
      have hz : ∀ j, raw9698step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9698step1 = (fun i j => raw9698step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9698step0 permutation151 hz
    injectiveMoment H raw9698step1 = injectiveMoment H raw9698step2 := by
      have heq : raw9698step2 = (fun i j => raw9698step1 (permutation112 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9698step1 permutation112 permutation5
    _ = injectiveMoment H node708 := by rfl

def raw9699 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-1, -2, 2, 1], ![1, 2, -2, -1]]

def raw9699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1]]

def raw9699step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw9699step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical9699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9699 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw9699 = injectiveMoment H raw9699step0 := by
      have heq : raw9699step0 = raw9699.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9699).symm
    injectiveMoment H raw9699step0 = injectiveMoment H raw9699step1 := by
      have hz : ∀ i, raw9699step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw9699step1 = (fun i j => raw9699step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9699step0 permutation3 hz
    injectiveMoment H raw9699step1 = injectiveMoment H raw9699step2 := by
      have heq : raw9699step2 = (fun i j => raw9699step1 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9699step1 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw9700 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9700step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9700step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9700 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9700 = injectiveMoment H node1523 := by
  calc
    injectiveMoment H raw9700 = injectiveMoment H raw9700step0 := by
      have hz : ∀ j, raw9700 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9700step0 = (fun i j => raw9700 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9700 permutation151 hz
    injectiveMoment H raw9700step0 = injectiveMoment H raw9700step1 := by
      have heq : raw9700step1 = (fun i j => raw9700step0 (permutation149 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9700step0 permutation149 permutation23
    _ = injectiveMoment H node1523 := by rfl

def raw9701 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9701step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9701step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9701 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9701 = injectiveMoment H node1507 := by
  calc
    injectiveMoment H raw9701 = injectiveMoment H raw9701step0 := by
      have hz : ∀ j, raw9701 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9701step0 = (fun i j => raw9701 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9701 permutation151 hz
    injectiveMoment H raw9701step0 = injectiveMoment H raw9701step1 := by
      have heq : raw9701step1 = (fun i j => raw9701step0 (permutation139 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9701step0 permutation139 permutation11
    _ = injectiveMoment H node1507 := by rfl

def raw9702 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9702step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9702step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical9702 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9702 = injectiveMoment H node1680 := by
  calc
    injectiveMoment H raw9702 = injectiveMoment H raw9702step0 := by
      have hz : ∀ j, raw9702 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9702step0 = (fun i j => raw9702 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9702 permutation151 hz
    injectiveMoment H raw9702step0 = injectiveMoment H raw9702step1 := by
      have heq : raw9702step1 = (fun i j => raw9702step0 (permutation104 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9702step0 permutation104 permutation9
    _ = injectiveMoment H node1680 := by rfl

def raw9703 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9703step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9703step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical9703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9703 = injectiveMoment H node1631 := by
  calc
    injectiveMoment H raw9703 = injectiveMoment H raw9703step0 := by
      have hz : ∀ j, raw9703 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9703step0 = (fun i j => raw9703 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9703 permutation151 hz
    injectiveMoment H raw9703step0 = injectiveMoment H raw9703step1 := by
      have heq : raw9703step1 = (fun i j => raw9703step0 (permutation112 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9703step0 permutation112 permutation11
    _ = injectiveMoment H node1631 := by rfl

def raw9704 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9704step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9704step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9704step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical9704 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9704 = injectiveMoment H node2742 := by
  calc
    injectiveMoment H raw9704 = injectiveMoment H raw9704step0 := by
      have heq : raw9704step0 = -raw9704 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9704).symm
    injectiveMoment H raw9704step0 = injectiveMoment H raw9704step1 := by
      have hz : ∀ j, raw9704step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9704step1 = (fun i j => raw9704step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9704step0 permutation151 hz
    injectiveMoment H raw9704step1 = injectiveMoment H raw9704step2 := by
      have heq : raw9704step2 = (fun i j => raw9704step1 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9704step1 permutation48 permutation21
    _ = injectiveMoment H node2742 := by rfl

def raw9705 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9705step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9705step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9705step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical9705 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9705 = injectiveMoment H node2739 := by
  calc
    injectiveMoment H raw9705 = injectiveMoment H raw9705step0 := by
      have heq : raw9705step0 = -raw9705 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9705).symm
    injectiveMoment H raw9705step0 = injectiveMoment H raw9705step1 := by
      have hz : ∀ j, raw9705step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9705step1 = (fun i j => raw9705step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9705step0 permutation151 hz
    injectiveMoment H raw9705step1 = injectiveMoment H raw9705step2 := by
      have heq : raw9705step2 = (fun i j => raw9705step1 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9705step1 permutation48 permutation21
    _ = injectiveMoment H node2739 := by rfl

def raw9706 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9706step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9706step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9706step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical9706 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9706 = injectiveMoment H node2748 := by
  calc
    injectiveMoment H raw9706 = injectiveMoment H raw9706step0 := by
      have heq : raw9706step0 = -raw9706 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9706).symm
    injectiveMoment H raw9706step0 = injectiveMoment H raw9706step1 := by
      have hz : ∀ j, raw9706step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9706step1 = (fun i j => raw9706step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9706step0 permutation151 hz
    injectiveMoment H raw9706step1 = injectiveMoment H raw9706step2 := by
      have heq : raw9706step2 = (fun i j => raw9706step1 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9706step1 permutation48 permutation21
    _ = injectiveMoment H node2748 := by rfl

def raw9707 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9707step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9707step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9707 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9707 = injectiveMoment H node2453 := by
  calc
    injectiveMoment H raw9707 = injectiveMoment H raw9707step0 := by
      have hz : ∀ j, raw9707 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9707step0 = (fun i j => raw9707 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9707 permutation151 hz
    injectiveMoment H raw9707step0 = injectiveMoment H raw9707step1 := by
      have heq : raw9707step1 = (fun i j => raw9707step0 (permutation148 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9707step0 permutation148 permutation23
    _ = injectiveMoment H node2453 := by rfl

def raw9708 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9708step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9708step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical9708 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9708 = injectiveMoment H node2421 := by
  calc
    injectiveMoment H raw9708 = injectiveMoment H raw9708step0 := by
      have hz : ∀ j, raw9708 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9708step0 = (fun i j => raw9708 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9708 permutation151 hz
    injectiveMoment H raw9708step0 = injectiveMoment H raw9708step1 := by
      have heq : raw9708step1 = (fun i j => raw9708step0 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9708step0 permutation136 permutation21
    _ = injectiveMoment H node2421 := by rfl

def raw9709 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9709step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9709step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9709 = injectiveMoment H node2676 := by
  calc
    injectiveMoment H raw9709 = injectiveMoment H raw9709step0 := by
      have hz : ∀ j, raw9709 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9709step0 = (fun i j => raw9709 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9709 permutation151 hz
    injectiveMoment H raw9709step0 = injectiveMoment H raw9709step1 := by
      have heq : raw9709step1 = (fun i j => raw9709step0 (permutation125 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9709step0 permutation125 permutation23
    _ = injectiveMoment H node2676 := by rfl

def raw9710 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9710step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9710step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9710step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical9710 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9710 = injectiveMoment H node2749 := by
  calc
    injectiveMoment H raw9710 = injectiveMoment H raw9710step0 := by
      have heq : raw9710step0 = -raw9710 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9710).symm
    injectiveMoment H raw9710step0 = injectiveMoment H raw9710step1 := by
      have hz : ∀ j, raw9710step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9710step1 = (fun i j => raw9710step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9710step0 permutation151 hz
    injectiveMoment H raw9710step1 = injectiveMoment H raw9710step2 := by
      have heq : raw9710step2 = (fun i j => raw9710step1 (permutation34 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9710step1 permutation34 permutation23
    _ = injectiveMoment H node2749 := by rfl

def raw9711 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9711step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9711step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9711 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw9711 = injectiveMoment H raw9711step0 := by
      have hz : ∀ j, raw9711 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9711step0 = (fun i j => raw9711 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9711 permutation151 hz
    injectiveMoment H raw9711step0 = injectiveMoment H raw9711step1 := by
      have heq : raw9711step1 = (fun i j => raw9711step0 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9711step0 permutation136 permutation21
    _ = injectiveMoment H node2448 := by rfl

def raw9712 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9712step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9712step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical9712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9712 = injectiveMoment H node2400 := by
  calc
    injectiveMoment H raw9712 = injectiveMoment H raw9712step0 := by
      have hz : ∀ j, raw9712 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9712step0 = (fun i j => raw9712 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9712 permutation151 hz
    injectiveMoment H raw9712step0 = injectiveMoment H raw9712step1 := by
      have heq : raw9712step1 = (fun i j => raw9712step0 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9712step0 permutation136 permutation21
    _ = injectiveMoment H node2400 := by rfl

def raw9713 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9713step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9713step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9713step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical9713 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9713 = injectiveMoment H node2747 := by
  calc
    injectiveMoment H raw9713 = injectiveMoment H raw9713step0 := by
      have heq : raw9713step0 = -raw9713 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9713).symm
    injectiveMoment H raw9713step0 = injectiveMoment H raw9713step1 := by
      have hz : ∀ j, raw9713step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9713step1 = (fun i j => raw9713step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9713step0 permutation151 hz
    injectiveMoment H raw9713step1 = injectiveMoment H raw9713step2 := by
      have heq : raw9713step2 = (fun i j => raw9713step1 (permutation46 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9713step1 permutation46 permutation23
    _ = injectiveMoment H node2747 := by rfl

def raw9714 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9714step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9714step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9714step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical9714 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9714 = injectiveMoment H node1739 := by
  calc
    injectiveMoment H raw9714 = injectiveMoment H raw9714step0 := by
      have heq : raw9714step0 = -raw9714 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9714).symm
    injectiveMoment H raw9714step0 = injectiveMoment H raw9714step1 := by
      have hz : ∀ j, raw9714step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9714step1 = (fun i j => raw9714step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9714step0 permutation151 hz
    injectiveMoment H raw9714step1 = injectiveMoment H raw9714step2 := by
      have heq : raw9714step2 = (fun i j => raw9714step1 (permutation130 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9714step1 permutation130 permutation17
    _ = injectiveMoment H node1739 := by rfl

def raw9715 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9715step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9715step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9715step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical9715 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9715 = injectiveMoment H node2740 := by
  calc
    injectiveMoment H raw9715 = injectiveMoment H raw9715step0 := by
      have heq : raw9715step0 = -raw9715 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9715).symm
    injectiveMoment H raw9715step0 = injectiveMoment H raw9715step1 := by
      have hz : ∀ j, raw9715step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9715step1 = (fun i j => raw9715step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9715step0 permutation151 hz
    injectiveMoment H raw9715step1 = injectiveMoment H raw9715step2 := by
      have heq : raw9715step2 = (fun i j => raw9715step1 (permutation46 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9715step1 permutation46 permutation23
    _ = injectiveMoment H node2740 := by rfl

def raw9716 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9716step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9716step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical9716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9716 = injectiveMoment H node2532 := by
  calc
    injectiveMoment H raw9716 = injectiveMoment H raw9716step0 := by
      have hz : ∀ j, raw9716 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9716step0 = (fun i j => raw9716 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9716 permutation151 hz
    injectiveMoment H raw9716step0 = injectiveMoment H raw9716step1 := by
      have heq : raw9716step1 = (fun i j => raw9716step0 (permutation136 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9716step0 permutation136 permutation23
    _ = injectiveMoment H node2532 := by rfl

def raw9717 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9717step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9717step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9717step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical9717 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9717 = injectiveMoment H node2750 := by
  calc
    injectiveMoment H raw9717 = injectiveMoment H raw9717step0 := by
      have heq : raw9717step0 = -raw9717 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9717).symm
    injectiveMoment H raw9717step0 = injectiveMoment H raw9717step1 := by
      have hz : ∀ j, raw9717step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9717step1 = (fun i j => raw9717step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9717step0 permutation151 hz
    injectiveMoment H raw9717step1 = injectiveMoment H raw9717step2 := by
      have heq : raw9717step2 = (fun i j => raw9717step1 (permutation40 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9717step1 permutation40 permutation21
    _ = injectiveMoment H node2750 := by rfl

def raw9718 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9718step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9718step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9718 = injectiveMoment H node2402 := by
  calc
    injectiveMoment H raw9718 = injectiveMoment H raw9718step0 := by
      have hz : ∀ j, raw9718 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9718step0 = (fun i j => raw9718 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9718 permutation151 hz
    injectiveMoment H raw9718step0 = injectiveMoment H raw9718step1 := by
      have heq : raw9718step1 = (fun i j => raw9718step0 (permutation148 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9718step0 permutation148 permutation21
    _ = injectiveMoment H node2402 := by rfl

def raw9719 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9719step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9719step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9719step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9719 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9719 = injectiveMoment H node1644 := by
  calc
    injectiveMoment H raw9719 = injectiveMoment H raw9719step0 := by
      have heq : raw9719step0 = -raw9719 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9719).symm
    injectiveMoment H raw9719step0 = injectiveMoment H raw9719step1 := by
      have hz : ∀ j, raw9719step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9719step1 = (fun i j => raw9719step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9719step0 permutation151 hz
    injectiveMoment H raw9719step1 = injectiveMoment H raw9719step2 := by
      have heq : raw9719step2 = (fun i j => raw9719step1 (permutation143 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9719step1 permutation143 permutation21
    _ = injectiveMoment H node1644 := by rfl

def raw9720 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9720step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9720step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem canonical9720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9720 = injectiveMoment H node1634 := by
  calc
    injectiveMoment H raw9720 = injectiveMoment H raw9720step0 := by
      have hz : ∀ j, raw9720 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9720step0 = (fun i j => raw9720 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9720 permutation151 hz
    injectiveMoment H raw9720step0 = injectiveMoment H raw9720step1 := by
      have heq : raw9720step1 = (fun i j => raw9720step0 (permutation104 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9720step0 permutation104 permutation11
    _ = injectiveMoment H node1634 := by rfl

def raw9721 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9721step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9721step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9721step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical9721 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9721 = injectiveMoment H node2607 := by
  calc
    injectiveMoment H raw9721 = injectiveMoment H raw9721step0 := by
      have heq : raw9721step0 = -raw9721 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9721).symm
    injectiveMoment H raw9721step0 = injectiveMoment H raw9721step1 := by
      have hz : ∀ j, raw9721step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9721step1 = (fun i j => raw9721step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9721step0 permutation151 hz
    injectiveMoment H raw9721step1 = injectiveMoment H raw9721step2 := by
      have heq : raw9721step2 = (fun i j => raw9721step1 (permutation144 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9721step1 permutation144 permutation26
    _ = injectiveMoment H node2607 := by rfl

def raw9722 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9722step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, -1, -2]]

def raw9722step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, -1, -2]]

def raw9722step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical9722 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9722 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw9722 = injectiveMoment H raw9722step0 := by
      have heq : raw9722step0 = -raw9722 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9722).symm
    injectiveMoment H raw9722step0 = injectiveMoment H raw9722step1 := by
      have hz : ∀ j, raw9722step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9722step1 = (fun i j => raw9722step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9722step0 permutation151 hz
    injectiveMoment H raw9722step1 = injectiveMoment H raw9722step2 := by
      have heq : raw9722step2 = (fun i j => raw9722step1 (permutation142 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9722step1 permutation142 permutation26
    _ = injectiveMoment H node2449 := by rfl

def raw9723 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9723step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9723step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9723 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9723 = injectiveMoment H node1644 := by
  calc
    injectiveMoment H raw9723 = injectiveMoment H raw9723step0 := by
      have hz : ∀ j, raw9723 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9723step0 = (fun i j => raw9723 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9723 permutation151 hz
    injectiveMoment H raw9723step0 = injectiveMoment H raw9723step1 := by
      have heq : raw9723step1 = (fun i j => raw9723step0 (permutation108 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9723step0 permutation108 permutation11
    _ = injectiveMoment H node1644 := by rfl

def raw9724 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9724step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9724step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9724 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9724 = injectiveMoment H node1720 := by
  calc
    injectiveMoment H raw9724 = injectiveMoment H raw9724step0 := by
      have hz : ∀ j, raw9724 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9724step0 = (fun i j => raw9724 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9724 permutation151 hz
    injectiveMoment H raw9724step0 = injectiveMoment H raw9724step1 := by
      have heq : raw9724step1 = (fun i j => raw9724step0 (permutation108 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9724step0 permutation108 permutation9
    _ = injectiveMoment H node1720 := by rfl

def raw9725 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9725step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -1, -2, 2]]

def raw9725step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -1, -2, 2]]

def raw9725step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical9725 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9725 = injectiveMoment H node1768 := by
  calc
    injectiveMoment H raw9725 = injectiveMoment H raw9725step0 := by
      have heq : raw9725step0 = -raw9725 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9725).symm
    injectiveMoment H raw9725step0 = injectiveMoment H raw9725step1 := by
      have hz : ∀ j, raw9725step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9725step1 = (fun i j => raw9725step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9725step0 permutation151 hz
    injectiveMoment H raw9725step1 = injectiveMoment H raw9725step2 := by
      have heq : raw9725step2 = (fun i j => raw9725step1 (permutation141 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9725step1 permutation141 permutation23
    _ = injectiveMoment H node1768 := by rfl

def raw9726 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9726step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2]]

def raw9726step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2]]

def raw9726step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9726 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9726 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw9726 = injectiveMoment H raw9726step0 := by
      have heq : raw9726step0 = -raw9726 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9726).symm
    injectiveMoment H raw9726step0 = injectiveMoment H raw9726step1 := by
      have hz : ∀ j, raw9726step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9726step1 = (fun i j => raw9726step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9726step0 permutation151 hz
    injectiveMoment H raw9726step1 = injectiveMoment H raw9726step2 := by
      have heq : raw9726step2 = (fun i j => raw9726step1 (permutation139 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9726step1 permutation139 permutation26
    _ = injectiveMoment H node2448 := by rfl

def raw9727 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9727step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9727step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical9727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9727 = injectiveMoment H node2390 := by
  calc
    injectiveMoment H raw9727 = injectiveMoment H raw9727step0 := by
      have hz : ∀ j, raw9727 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9727step0 = (fun i j => raw9727 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9727 permutation151 hz
    injectiveMoment H raw9727step0 = injectiveMoment H raw9727step1 := by
      have heq : raw9727step1 = (fun i j => raw9727step0 (permutation128 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9727step0 permutation128 permutation21
    _ = injectiveMoment H node2390 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
