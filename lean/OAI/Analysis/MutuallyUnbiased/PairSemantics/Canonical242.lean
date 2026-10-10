import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7744 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![-2, 2]]

def raw7744step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7744 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7744 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7744 = injectiveMoment H raw7744step0 := by
      have heq : raw7744step0 = (fun i j => raw7744 (permutation128 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7744 permutation128 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw7745 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![0, 0], ![1, -1]]

def raw7745step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7745step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7745 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7745 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7745 = injectiveMoment H raw7745step0 := by
      have hz : ∀ j, raw7745 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7745step0 = (fun i j => raw7745 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7745 permutation104 hz
    injectiveMoment H raw7745step0 = injectiveMoment H raw7745step1 := by
      have heq : raw7745step1 = (fun i j => raw7745step0 (permutation22 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7745step0 permutation22 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7746 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7746step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7746 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7746 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7746 = injectiveMoment H raw7746step0 := by
      have heq : raw7746step0 = (fun i j => raw7746 (permutation22 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7746 permutation22 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7747 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1], ![0, 0]]

def raw7747step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7747step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7747 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7747 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7747 = injectiveMoment H raw7747step0 := by
      have hz : ∀ j, raw7747 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7747step0 = (fun i j => raw7747 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7747 permutation128 hz
    injectiveMoment H raw7747step0 = injectiveMoment H raw7747step1 := by
      have heq : raw7747step1 = (fun i j => raw7747step0 (permutation22 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7747step0 permutation22 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7748 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1], ![0, 0], ![0, 0]]

def raw7748step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1], ![0, 0]]

def raw7748step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7748step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7748 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7748 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7748 = injectiveMoment H raw7748step0 := by
      have hz : ∀ j, raw7748 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7748step0 = (fun i j => raw7748 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7748 permutation308 hz
    injectiveMoment H raw7748step0 = injectiveMoment H raw7748step1 := by
      have hz : ∀ j, raw7748step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7748step1 = (fun i j => raw7748step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7748step0 permutation128 hz
    injectiveMoment H raw7748step1 = injectiveMoment H raw7748step2 := by
      have heq : raw7748step2 = (fun i j => raw7748step1 (permutation22 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7748step1 permutation22 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7749 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7749step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7749 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7749 = injectiveMoment H raw7749step0 := by
      have heq : raw7749step0 = (fun i j => raw7749 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7749 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7750 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7750step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7750step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7750 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7750 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7750 = injectiveMoment H raw7750step0 := by
      have hz : ∀ j, raw7750 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7750step0 = (fun i j => raw7750 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7750 permutation258 hz
    injectiveMoment H raw7750step0 = injectiveMoment H raw7750step1 := by
      have heq : raw7750step1 = (fun i j => raw7750step0 (permutation74 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7750step0 permutation74 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7751 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7751step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7751 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7751 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7751 = injectiveMoment H raw7751step0 := by
      have heq : raw7751step0 = (fun i j => raw7751 (permutation74 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7751 permutation74 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7752 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0]]

def raw7752step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7752step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7752 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7752 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7752 = injectiveMoment H raw7752step0 := by
      have hz : ∀ j, raw7752 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7752step0 = (fun i j => raw7752 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7752 permutation308 hz
    injectiveMoment H raw7752step0 = injectiveMoment H raw7752step1 := by
      have heq : raw7752step1 = (fun i j => raw7752step0 (permutation74 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7752step0 permutation74 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7753 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw7753step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7753step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7753 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7753 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7753 = injectiveMoment H raw7753step0 := by
      have hz : ∀ j, raw7753 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7753step0 = (fun i j => raw7753 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7753 permutation27 hz
    injectiveMoment H raw7753step0 = injectiveMoment H raw7753step1 := by
      have heq : raw7753step1 = (fun i j => raw7753step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7753step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7754 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0], ![0, 0]]

def raw7754step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw7754step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7754step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7754 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7754 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7754 = injectiveMoment H raw7754step0 := by
      have hz : ∀ j, raw7754 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7754step0 = (fun i j => raw7754 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7754 permutation128 hz
    injectiveMoment H raw7754step0 = injectiveMoment H raw7754step1 := by
      have hz : ∀ j, raw7754step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7754step1 = (fun i j => raw7754step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7754step0 permutation27 hz
    injectiveMoment H raw7754step1 = injectiveMoment H raw7754step2 := by
      have heq : raw7754step2 = (fun i j => raw7754step1 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7754step1 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7755 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0], ![0, 0], ![0, 0]]

def raw7755step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0], ![0, 0]]

def raw7755step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw7755step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7755step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7755 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7755 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7755 = injectiveMoment H raw7755step0 := by
      have hz : ∀ j, raw7755 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7755step0 = (fun i j => raw7755 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7755 permutation308 hz
    injectiveMoment H raw7755step0 = injectiveMoment H raw7755step1 := by
      have hz : ∀ j, raw7755step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7755step1 = (fun i j => raw7755step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7755step0 permutation128 hz
    injectiveMoment H raw7755step1 = injectiveMoment H raw7755step2 := by
      have hz : ∀ j, raw7755step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7755step2 = (fun i j => raw7755step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7755step1 permutation27 hz
    injectiveMoment H raw7755step2 = injectiveMoment H raw7755step3 := by
      have heq : raw7755step3 = (fun i j => raw7755step2 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7755step2 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7756 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7756step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![-1, 1]]

def raw7756step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7756 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7756 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7756 = injectiveMoment H raw7756step0 := by
      have hz : ∀ j, raw7756 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7756step0 = (fun i j => raw7756 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7756 permutation258 hz
    injectiveMoment H raw7756step0 = injectiveMoment H raw7756step1 := by
      have heq : raw7756step1 = (fun i j => raw7756step0 (permutation68 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7756step0 permutation68 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7757 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def raw7757step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7757step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7757 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7757 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7757 = injectiveMoment H raw7757step0 := by
      have hz : ∀ j, raw7757 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7757step0 = (fun i j => raw7757 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7757 permutation21 hz
    injectiveMoment H raw7757step0 = injectiveMoment H raw7757step1 := by
      have heq : raw7757step1 = (fun i j => raw7757step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7757step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7758 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![-1, 1]]

def raw7758step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def raw7758step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7758step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7758 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7758 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7758 = injectiveMoment H raw7758step0 := by
      have hz : ∀ j, raw7758 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7758step0 = (fun i j => raw7758 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7758 permutation104 hz
    injectiveMoment H raw7758step0 = injectiveMoment H raw7758step1 := by
      have hz : ∀ j, raw7758step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7758step1 = (fun i j => raw7758step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7758step0 permutation21 hz
    injectiveMoment H raw7758step1 = injectiveMoment H raw7758step2 := by
      have heq : raw7758step2 = (fun i j => raw7758step1 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7758step1 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7759 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-2, 2], ![0, 0], ![0, 0]]

def raw7759step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-2, 2], ![0, 0]]

def raw7759step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-2, 2]]

def raw7759step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7759 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7759 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7759 = injectiveMoment H raw7759step0 := by
      have hz : ∀ j, raw7759 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7759step0 = (fun i j => raw7759 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7759 permutation308 hz
    injectiveMoment H raw7759step0 = injectiveMoment H raw7759step1 := by
      have hz : ∀ j, raw7759step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7759step1 = (fun i j => raw7759step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7759step0 permutation128 hz
    injectiveMoment H raw7759step1 = injectiveMoment H raw7759step2 := by
      have heq : raw7759step2 = (fun i j => raw7759step1 (permutation28 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7759step1 permutation28 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7760 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-1, 1], ![-1, 1]]

def raw7760step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7760 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7760 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7760 = injectiveMoment H raw7760step0 := by
      have heq : raw7760step0 = (fun i j => raw7760 (permutation63 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7760 permutation63 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7761 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![3, -3], ![-1, 1], ![-1, 1]]

def raw7761step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7761 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw7761 = injectiveMoment H raw7761step0 := by
      have heq : raw7761step0 = (fun i j => raw7761 (permutation15 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7761 permutation15 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw7762 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, 0, 2, -2], ![1, -1, 2, -2]]

def raw7762step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-4, 2, 2], ![4, -2, -2]]

def raw7762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![2, 2, -4]]

theorem canonical7762 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7762 = injectiveMoment H node139 := by
  calc
    injectiveMoment H raw7762 = injectiveMoment H raw7762step0 := by
      have heq : raw7762step0 = raw7762.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7762).symm
    injectiveMoment H raw7762step0 = injectiveMoment H raw7762step1 := by
      have heq : raw7762step1 = (fun i j => raw7762step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7762step0 permutation29 permutation6
    _ = injectiveMoment H node139 := by rfl

def raw7763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical7763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7763 = injectiveMoment H node2833 := by
  rfl

def raw7764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw7764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical7764 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7764 = injectiveMoment H node2833 := by
  calc
    injectiveMoment H raw7764 = injectiveMoment H raw7764step0 := by
      have heq : raw7764step0 = (fun i j => raw7764 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7764 permutation34 permutation9
    _ = injectiveMoment H node2833 := by rfl

def raw7765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical7765 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7765 = injectiveMoment H node2834 := by
  rfl

def raw7766 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw7766step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 1, 0, -2], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw7766step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem canonical7766 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7766 = injectiveMoment H node471 := by
  calc
    injectiveMoment H raw7766 = injectiveMoment H raw7766step0 := by
      have heq : raw7766step0 = raw7766.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7766).symm
    injectiveMoment H raw7766step0 = injectiveMoment H raw7766step1 := by
      have heq : raw7766step1 = (fun i j => raw7766step0 (permutation27 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7766step0 permutation27 permutation24
    _ = injectiveMoment H node471 := by rfl

def raw7767 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7767step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 1, 0, 2], ![3, -1, 0, -2]]

def raw7767step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical7767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7767 = injectiveMoment H node1339 := by
  calc
    injectiveMoment H raw7767 = injectiveMoment H raw7767step0 := by
      have heq : raw7767step0 = raw7767.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7767).symm
    injectiveMoment H raw7767step0 = injectiveMoment H raw7767step1 := by
      have heq : raw7767step1 = (fun i j => raw7767step0 (permutation20 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7767step0 permutation20 permutation24
    _ = injectiveMoment H node1339 := by rfl

def raw7768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 1, 1, 1], ![3, -1, -1, -1]]

def raw7768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical7768 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7768 = injectiveMoment H node924 := by
  calc
    injectiveMoment H raw7768 = injectiveMoment H raw7768step0 := by
      have heq : raw7768step0 = raw7768.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7768).symm
    injectiveMoment H raw7768step0 = injectiveMoment H raw7768step1 := by
      have heq : raw7768step1 = (fun i j => raw7768step0 (permutation29 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7768step0 permutation29 permutation26
    _ = injectiveMoment H node924 := by rfl

def raw7769 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, -1, 0, 0]]

def raw7769step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw7769step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical7769 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7769 = injectiveMoment H node1339 := by
  calc
    injectiveMoment H raw7769 = injectiveMoment H raw7769step0 := by
      have heq : raw7769step0 = raw7769.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7769).symm
    injectiveMoment H raw7769step0 = injectiveMoment H raw7769step1 := by
      have heq : raw7769step1 = (fun i j => raw7769step0 (permutation20 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7769step0 permutation20 permutation30
    _ = injectiveMoment H node1339 := by rfl

def raw7770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical7770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7770 = injectiveMoment H node2835 := by
  rfl

def raw7771 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7771step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 2, 0, 1], ![3, -2, 0, -1]]

def raw7771step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical7771 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7771 = injectiveMoment H node1092 := by
  calc
    injectiveMoment H raw7771 = injectiveMoment H raw7771step0 := by
      have heq : raw7771step0 = raw7771.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7771).symm
    injectiveMoment H raw7771step0 = injectiveMoment H raw7771step1 := by
      have heq : raw7771step1 = (fun i j => raw7771step0 (permutation20 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7771step0 permutation20 permutation26
    _ = injectiveMoment H node1092 := by rfl

def raw7772 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw7772step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 2, 1, 0], ![3, -2, -1, 0]]

def raw7772step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical7772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7772 = injectiveMoment H node1092 := by
  calc
    injectiveMoment H raw7772 = injectiveMoment H raw7772step0 := by
      have heq : raw7772step0 = raw7772.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7772).symm
    injectiveMoment H raw7772step0 = injectiveMoment H raw7772step1 := by
      have heq : raw7772step1 = (fun i j => raw7772step0 (permutation20 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7772step0 permutation20 permutation32
    _ = injectiveMoment H node1092 := by rfl

def raw7773 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7773step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 3, 0, 0], ![3, -3, 0, 0]]

def raw7773step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical7773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7773 = injectiveMoment H node1101 := by
  calc
    injectiveMoment H raw7773 = injectiveMoment H raw7773step0 := by
      have heq : raw7773step0 = raw7773.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7773).symm
    injectiveMoment H raw7773step0 = injectiveMoment H raw7773step1 := by
      have heq : raw7773step1 = (fun i j => raw7773step0 (permutation18 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7773step0 permutation18 permutation25
    _ = injectiveMoment H node1101 := by rfl

def raw7774 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7774step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 1, 0], ![-3, 3, 0, 0], ![3, -1, -1, -1]]

def raw7774step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical7774 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7774 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw7774 = injectiveMoment H raw7774step0 := by
      have heq : raw7774step0 = raw7774.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7774).symm
    injectiveMoment H raw7774step0 = injectiveMoment H raw7774step1 := by
      have heq : raw7774step1 = (fun i j => raw7774step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7774step0 permutation32 permutation32
    _ = injectiveMoment H node977 := by rfl

def raw7775 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw7775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-3, 2, 1], ![3, -1, -2]]

def raw7775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7775 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw7775 = injectiveMoment H raw7775step0 := by
      have heq : raw7775step0 = raw7775.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7775).symm
    injectiveMoment H raw7775step0 = injectiveMoment H raw7775step1 := by
      have heq : raw7775step1 = (fun i j => raw7775step0 (permutation29 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7775step0 permutation29 permutation8
    _ = injectiveMoment H node174 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
