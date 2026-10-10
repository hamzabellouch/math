import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9792 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, -1, 2], ![2, -2, -2, 2]]

def raw9792step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

theorem canonical9792 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9792 = injectiveMoment H node3265 := by
  calc
    injectiveMoment H raw9792 = injectiveMoment H raw9792step0 := by
      have heq : raw9792step0 = (fun i j => raw9792 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9792 permutation258 permutation9
    _ = injectiveMoment H node3265 := by rfl

def raw9793 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -3, 3]]

def raw9793step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

theorem canonical9793 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9793 = injectiveMoment H node3294 := by
  calc
    injectiveMoment H raw9793 = injectiveMoment H raw9793step0 := by
      have heq : raw9793step0 = (fun i j => raw9793 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9793 permutation258 permutation9
    _ = injectiveMoment H node3294 := by rfl

def raw9794 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 1, -2, 3]]

def raw9794step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

theorem canonical9794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9794 = injectiveMoment H node3241 := by
  calc
    injectiveMoment H raw9794 = injectiveMoment H raw9794step0 := by
      have heq : raw9794step0 = (fun i j => raw9794 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9794 permutation308 permutation9
    _ = injectiveMoment H node3241 := by rfl

def raw9795 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -3, 4]]

def raw9795step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

theorem canonical9795 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9795 = injectiveMoment H node3223 := by
  calc
    injectiveMoment H raw9795 = injectiveMoment H raw9795step0 := by
      have heq : raw9795step0 = (fun i j => raw9795 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9795 permutation308 permutation9
    _ = injectiveMoment H node3223 := by rfl

def raw9796 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![-1, 1, 0, 0], ![1, -2, 1, 0]]

def raw9796step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical9796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9796 = injectiveMoment H node2812 := by
  calc
    injectiveMoment H raw9796 = injectiveMoment H raw9796step0 := by
      have heq : raw9796step0 = (fun i j => raw9796 (permutation104 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9796 permutation104 permutation13
    _ = injectiveMoment H node2812 := by rfl

def raw9797 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![0, -2, 1, 1]]

def raw9797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![-2, 1, 1]]

def raw9797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical9797 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9797 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw9797 = injectiveMoment H raw9797step0 := by
      have hz : ∀ i, raw9797 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9797step0 = (fun i j => raw9797 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9797 permutation9 hz
    injectiveMoment H raw9797step0 = injectiveMoment H raw9797step1 := by
      have heq : raw9797step1 = (fun i j => raw9797step0 (permutation129 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9797step0 permutation129 permutation4
    _ = injectiveMoment H node708 := by rfl

def raw9798 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9798step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical9798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9798 = injectiveMoment H node2993 := by
  calc
    injectiveMoment H raw9798 = injectiveMoment H raw9798step0 := by
      have heq : raw9798step0 = (fun i j => raw9798 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9798 permutation258 permutation9
    _ = injectiveMoment H node2993 := by rfl

def raw9799 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9799step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

theorem canonical9799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9799 = injectiveMoment H node3134 := by
  calc
    injectiveMoment H raw9799 = injectiveMoment H raw9799step0 := by
      have heq : raw9799step0 = (fun i j => raw9799 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9799 permutation258 permutation9
    _ = injectiveMoment H node3134 := by rfl

def raw9800 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9800step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical9800 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9800 = injectiveMoment H node2994 := by
  calc
    injectiveMoment H raw9800 = injectiveMoment H raw9800step0 := by
      have heq : raw9800step0 = (fun i j => raw9800 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9800 permutation308 permutation9
    _ = injectiveMoment H node2994 := by rfl

def raw9801 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9801step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9801 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9801 = injectiveMoment H node2870 := by
  calc
    injectiveMoment H raw9801 = injectiveMoment H raw9801step0 := by
      have heq : raw9801step0 = (fun i j => raw9801 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9801 permutation308 permutation9
    _ = injectiveMoment H node2870 := by rfl

def raw9802 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9802step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical9802 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9802 = injectiveMoment H node2995 := by
  calc
    injectiveMoment H raw9802 = injectiveMoment H raw9802step0 := by
      have heq : raw9802step0 = (fun i j => raw9802 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9802 permutation308 permutation9
    _ = injectiveMoment H node2995 := by rfl

def raw9803 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, -1, 2]]

def raw9803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2]]

def raw9803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical9803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9803 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw9803 = injectiveMoment H raw9803step0 := by
      have hz : ∀ i, raw9803 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9803step0 = (fun i j => raw9803 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9803 permutation9 hz
    injectiveMoment H raw9803step0 = injectiveMoment H raw9803step1 := by
      have heq : raw9803step1 = (fun i j => raw9803step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9803step0 permutation27 permutation3
    _ = injectiveMoment H node287 := by rfl

def raw9804 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9804step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical9804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9804 = injectiveMoment H node2993 := by
  calc
    injectiveMoment H raw9804 = injectiveMoment H raw9804step0 := by
      have heq : raw9804step0 = (fun i j => raw9804 (permutation260 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9804 permutation260 permutation9
    _ = injectiveMoment H node2993 := by rfl

def raw9805 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, -1, 4], ![2, -1, 1, -2]]

def raw9805step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical9805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9805 = injectiveMoment H node2925 := by
  calc
    injectiveMoment H raw9805 = injectiveMoment H raw9805step0 := by
      have heq : raw9805step0 = (fun i j => raw9805 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9805 permutation258 permutation9
    _ = injectiveMoment H node2925 := by rfl

def raw9806 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 0, -1]]

def raw9806step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical9806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9806 = injectiveMoment H node2996 := by
  calc
    injectiveMoment H raw9806 = injectiveMoment H raw9806step0 := by
      have heq : raw9806step0 = (fun i j => raw9806 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9806 permutation258 permutation9
    _ = injectiveMoment H node2996 := by rfl

def raw9807 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9807step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical9807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9807 = injectiveMoment H node3135 := by
  calc
    injectiveMoment H raw9807 = injectiveMoment H raw9807step0 := by
      have heq : raw9807step0 = (fun i j => raw9807 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9807 permutation258 permutation9
    _ = injectiveMoment H node3135 := by rfl

def raw9808 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9808step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical9808 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9808 = injectiveMoment H node2996 := by
  calc
    injectiveMoment H raw9808 = injectiveMoment H raw9808step0 := by
      have heq : raw9808step0 = (fun i j => raw9808 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9808 permutation308 permutation9
    _ = injectiveMoment H node2996 := by rfl

def raw9809 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9809step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical9809 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9809 = injectiveMoment H node2872 := by
  calc
    injectiveMoment H raw9809 = injectiveMoment H raw9809step0 := by
      have heq : raw9809step0 = (fun i j => raw9809 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9809 permutation308 permutation9
    _ = injectiveMoment H node2872 := by rfl

def raw9810 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -2, 4], ![2, -2, 1, -1]]

def raw9810step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

theorem canonical9810 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9810 = injectiveMoment H node3118 := by
  calc
    injectiveMoment H raw9810 = injectiveMoment H raw9810step0 := by
      have heq : raw9810step0 = (fun i j => raw9810 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9810 permutation258 permutation9
    _ = injectiveMoment H node3118 := by rfl

def raw9811 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 0, 0]]

def raw9811step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9811 = injectiveMoment H node2966 := by
  calc
    injectiveMoment H raw9811 = injectiveMoment H raw9811step0 := by
      have heq : raw9811step0 = (fun i j => raw9811 (permutation286 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9811 permutation286 permutation11
    _ = injectiveMoment H node2966 := by rfl

def raw9812 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9812step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9812 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9812 = injectiveMoment H node3098 := by
  calc
    injectiveMoment H raw9812 = injectiveMoment H raw9812step0 := by
      have heq : raw9812step0 = (fun i j => raw9812 (permutation395 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9812 permutation395 permutation17
    _ = injectiveMoment H node3098 := by rfl

def raw9813 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9813step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9813 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9813 = injectiveMoment H node2966 := by
  calc
    injectiveMoment H raw9813 = injectiveMoment H raw9813step0 := by
      have heq : raw9813step0 = (fun i j => raw9813 (permutation363 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9813 permutation363 permutation11
    _ = injectiveMoment H node2966 := by rfl

def raw9814 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9814step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9814 = injectiveMoment H node2997 := by
  calc
    injectiveMoment H raw9814 = injectiveMoment H raw9814step0 := by
      have heq : raw9814step0 = (fun i j => raw9814 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9814 permutation308 permutation9
    _ = injectiveMoment H node2997 := by rfl

def raw9815 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, -1, 4]]

def raw9815step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9815 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9815 = injectiveMoment H node2911 := by
  calc
    injectiveMoment H raw9815 = injectiveMoment H raw9815step0 := by
      have heq : raw9815step0 = (fun i j => raw9815 (permutation363 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9815 permutation363 permutation11
    _ = injectiveMoment H node2911 := by rfl

def raw9816 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9816step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9816 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9816 = injectiveMoment H node2873 := by
  calc
    injectiveMoment H raw9816 = injectiveMoment H raw9816step0 := by
      have heq : raw9816step0 = (fun i j => raw9816 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9816 permutation308 permutation9
    _ = injectiveMoment H node2873 := by rfl

def raw9817 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, -1, 5]]

def raw9817step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9817 = injectiveMoment H node2863 := by
  calc
    injectiveMoment H raw9817 = injectiveMoment H raw9817step0 := by
      have heq : raw9817step0 = (fun i j => raw9817 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9817 permutation308 permutation9
    _ = injectiveMoment H node2863 := by rfl

def raw9818 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw9818step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem canonical9818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9818 = injectiveMoment H node3045 := by
  calc
    injectiveMoment H raw9818 = injectiveMoment H raw9818step0 := by
      have heq : raw9818step0 = (fun i j => raw9818 (permutation355 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9818 permutation355 permutation11
    _ = injectiveMoment H node3045 := by rfl

def raw9819 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9819step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical9819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9819 = injectiveMoment H node2998 := by
  calc
    injectiveMoment H raw9819 = injectiveMoment H raw9819step0 := by
      have heq : raw9819step0 = (fun i j => raw9819 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9819 permutation308 permutation9
    _ = injectiveMoment H node2998 := by rfl

def raw9820 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9820step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9820 = injectiveMoment H node3046 := by
  calc
    injectiveMoment H raw9820 = injectiveMoment H raw9820step0 := by
      have heq : raw9820step0 = (fun i j => raw9820 (permutation355 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9820 permutation355 permutation11
    _ = injectiveMoment H node3046 := by rfl

def raw9821 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3]]

def raw9821step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical9821 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9821 = injectiveMoment H node3457 := by
  calc
    injectiveMoment H raw9821 = injectiveMoment H raw9821step0 := by
      have heq : raw9821step0 = (fun i j => raw9821 (permutation257 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9821 permutation257 permutation17
    _ = injectiveMoment H node3457 := by rfl

def raw9822 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1], ![-2, -1, 0, 3]]

def raw9822step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9822 = injectiveMoment H node2999 := by
  calc
    injectiveMoment H raw9822 = injectiveMoment H raw9822step0 := by
      have heq : raw9822step0 = (fun i j => raw9822 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9822 permutation308 permutation9
    _ = injectiveMoment H node2999 := by rfl

def raw9823 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9823step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical9823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9823 = injectiveMoment H node2920 := by
  calc
    injectiveMoment H raw9823 = injectiveMoment H raw9823step0 := by
      have heq : raw9823step0 = (fun i j => raw9823 (permutation355 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9823 permutation355 permutation11
    _ = injectiveMoment H node2920 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
