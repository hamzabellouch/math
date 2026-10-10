import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
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

def raw9632 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9632step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical9632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9632 = injectiveMoment H node3080 := by
  calc
    injectiveMoment H raw9632 = injectiveMoment H raw9632step0 := by
      have heq : raw9632step0 = (fun i j => raw9632 (permutation309 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9632 permutation309 permutation10
    _ = injectiveMoment H node3080 := by rfl

def raw9633 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9633step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical9633 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9633 = injectiveMoment H node2992 := by
  calc
    injectiveMoment H raw9633 = injectiveMoment H raw9633step0 := by
      have heq : raw9633step0 = (fun i j => raw9633 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9633 permutation259 permutation9
    _ = injectiveMoment H node2992 := by rfl

def raw9634 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9634step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical9634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9634 = injectiveMoment H node3142 := by
  calc
    injectiveMoment H raw9634 = injectiveMoment H raw9634step0 := by
      have heq : raw9634step0 = (fun i j => raw9634 (permutation259 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9634 permutation259 permutation10
    _ = injectiveMoment H node3142 := by rfl

def raw9635 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, -1, 2], ![-2, 0, 3, -1]]

def raw9635step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical9635 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9635 = injectiveMoment H node3142 := by
  calc
    injectiveMoment H raw9635 = injectiveMoment H raw9635step0 := by
      have heq : raw9635step0 = (fun i j => raw9635 (permutation309 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9635 permutation309 permutation10
    _ = injectiveMoment H node3142 := by rfl

def raw9636 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 2, 0]]

def raw9636step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical9636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9636 = injectiveMoment H node3170 := by
  calc
    injectiveMoment H raw9636 = injectiveMoment H raw9636step0 := by
      have heq : raw9636step0 = (fun i j => raw9636 (permutation337 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9636 permutation337 permutation13
    _ = injectiveMoment H node3170 := by rfl

def raw9637 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 0, 0], ![-2, -1, 2, 1]]

def raw9637step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9637 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9637 = injectiveMoment H node3081 := by
  calc
    injectiveMoment H raw9637 = injectiveMoment H raw9637step0 := by
      have heq : raw9637step0 = (fun i j => raw9637 (permutation309 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9637 permutation309 permutation10
    _ = injectiveMoment H node3081 := by rfl

def raw9638 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9638step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical9638 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9638 = injectiveMoment H node3078 := by
  calc
    injectiveMoment H raw9638 = injectiveMoment H raw9638step0 := by
      have heq : raw9638step0 = (fun i j => raw9638 (permutation309 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9638 permutation309 permutation9
    _ = injectiveMoment H node3078 := by rfl

def raw9639 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9639step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9639 = injectiveMoment H node2894 := by
  calc
    injectiveMoment H raw9639 = injectiveMoment H raw9639step0 := by
      have heq : raw9639step0 = (fun i j => raw9639 (permutation324 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9639 permutation324 permutation15
    _ = injectiveMoment H node2894 := by rfl

def raw9640 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, -1, 4], ![1, -1, 2, -2]]

def raw9640step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

theorem canonical9640 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9640 = injectiveMoment H node2897 := by
  calc
    injectiveMoment H raw9640 = injectiveMoment H raw9640step0 := by
      have heq : raw9640step0 = (fun i j => raw9640 (permutation258 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9640 permutation258 permutation11
    _ = injectiveMoment H node2897 := by rfl

def raw9641 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 1, -1]]

def raw9641step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![-1, 1, -1, 1]]

def raw9641step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical9641 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9641 = injectiveMoment H node3400 := by
  calc
    injectiveMoment H raw9641 = injectiveMoment H raw9641step0 := by
      have heq : raw9641step0 = -raw9641 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9641).symm
    injectiveMoment H raw9641step0 = injectiveMoment H raw9641step1 := by
      have heq : raw9641step1 = (fun i j => raw9641step0 (permutation380 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9641step0 permutation380 permutation21
    _ = injectiveMoment H node3400 := by rfl

def raw9642 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9642step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9642 = injectiveMoment H node3033 := by
  calc
    injectiveMoment H raw9642 = injectiveMoment H raw9642step0 := by
      have heq : raw9642step0 = (fun i j => raw9642 (permutation324 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9642 permutation324 permutation17
    _ = injectiveMoment H node3033 := by rfl

def raw9643 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -2, 3]]

def raw9643step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

theorem canonical9643 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9643 = injectiveMoment H node3221 := by
  calc
    injectiveMoment H raw9643 = injectiveMoment H raw9643step0 := by
      have heq : raw9643step0 = (fun i j => raw9643 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9643 permutation259 permutation9
    _ = injectiveMoment H node3221 := by rfl

def raw9644 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 0, 0], ![-2, -1, 1, 2]]

def raw9644step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical9644 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9644 = injectiveMoment H node3446 := by
  calc
    injectiveMoment H raw9644 = injectiveMoment H raw9644step0 := by
      have heq : raw9644step0 = (fun i j => raw9644 (permutation192 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9644 permutation192 permutation23
    _ = injectiveMoment H node3446 := by rfl

def raw9645 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 0, 3]]

def raw9645step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 1, -1, 1], ![2, 1, 0, -3]]

def raw9645step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical9645 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9645 = injectiveMoment H node3400 := by
  calc
    injectiveMoment H raw9645 = injectiveMoment H raw9645step0 := by
      have heq : raw9645step0 = -raw9645 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9645).symm
    injectiveMoment H raw9645step0 = injectiveMoment H raw9645step1 := by
      have heq : raw9645step1 = (fun i j => raw9645step0 (permutation291 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9645step0 permutation291 permutation21
    _ = injectiveMoment H node3400 := by rfl

def raw9646 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0], ![-2, -2, 2, 2]]

def raw9646step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9646 = injectiveMoment H node2894 := by
  calc
    injectiveMoment H raw9646 = injectiveMoment H raw9646step0 := by
      have heq : raw9646step0 = (fun i j => raw9646 (permutation329 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9646 permutation329 permutation15
    _ = injectiveMoment H node2894 := by rfl

def raw9647 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9647step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical9647 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9647 = injectiveMoment H node3453 := by
  calc
    injectiveMoment H raw9647 = injectiveMoment H raw9647step0 := by
      have heq : raw9647step0 = (fun i j => raw9647 (permutation151 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9647 permutation151 permutation21
    _ = injectiveMoment H node3453 := by rfl

def raw9648 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -2, 0, 2]]

def raw9648step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 2, 0, -2]]

def raw9648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2]]

def raw9648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical9648 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9648 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw9648 = injectiveMoment H raw9648step0 := by
      have heq : raw9648step0 = -raw9648 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9648).symm
    injectiveMoment H raw9648step0 = injectiveMoment H raw9648step1 := by
      have hz : ∀ i, raw9648step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9648step1 = (fun i j => raw9648step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9648step0 permutation9 hz
    injectiveMoment H raw9648step1 = injectiveMoment H raw9648step2 := by
      have heq : raw9648step2 = (fun i j => raw9648step1 (permutation24 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9648step1 permutation24 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw9649 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9649step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9649step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9649 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9649 = injectiveMoment H node2950 := by
  calc
    injectiveMoment H raw9649 = injectiveMoment H raw9649step0 := by
      have heq : raw9649step0 = -raw9649 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9649).symm
    injectiveMoment H raw9649step0 = injectiveMoment H raw9649step1 := by
      have heq : raw9649step1 = (fun i j => raw9649step0 (permutation353 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9649step0 permutation353 permutation23
    _ = injectiveMoment H node2950 := by rfl

def raw9650 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9650step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9650 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9650 = injectiveMoment H node3264 := by
  calc
    injectiveMoment H raw9650 = injectiveMoment H raw9650step0 := by
      have heq : raw9650step0 = (fun i j => raw9650 (permutation275 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9650 permutation275 permutation9
    _ = injectiveMoment H node3264 := by rfl

def raw9651 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9651step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9651 = injectiveMoment H node3282 := by
  calc
    injectiveMoment H raw9651 = injectiveMoment H raw9651step0 := by
      have heq : raw9651step0 = (fun i j => raw9651 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9651 permutation294 permutation9
    _ = injectiveMoment H node3282 := by rfl

def raw9652 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9652step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

theorem canonical9652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9652 = injectiveMoment H node3379 := by
  calc
    injectiveMoment H raw9652 = injectiveMoment H raw9652step0 := by
      have heq : raw9652step0 = (fun i j => raw9652 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9652 permutation285 permutation15
    _ = injectiveMoment H node3379 := by rfl

def raw9653 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9653step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw9653step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9653 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9653 = injectiveMoment H node2942 := by
  calc
    injectiveMoment H raw9653 = injectiveMoment H raw9653step0 := by
      have heq : raw9653step0 = -raw9653 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9653).symm
    injectiveMoment H raw9653step0 = injectiveMoment H raw9653step1 := by
      have heq : raw9653step1 = (fun i j => raw9653step0 (permutation347 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9653step0 permutation347 permutation23
    _ = injectiveMoment H node2942 := by rfl

def raw9654 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9654step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9654step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9654 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9654 = injectiveMoment H node3026 := by
  calc
    injectiveMoment H raw9654 = injectiveMoment H raw9654step0 := by
      have heq : raw9654step0 = -raw9654 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9654).symm
    injectiveMoment H raw9654step0 = injectiveMoment H raw9654step1 := by
      have heq : raw9654step1 = (fun i j => raw9654step0 (permutation347 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9654step0 permutation347 permutation23
    _ = injectiveMoment H node3026 := by rfl

def raw9655 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9655step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9655 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9655 = injectiveMoment H node3305 := by
  calc
    injectiveMoment H raw9655 = injectiveMoment H raw9655step0 := by
      have heq : raw9655step0 = (fun i j => raw9655 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9655 permutation395 permutation9
    _ = injectiveMoment H node3305 := by rfl

def raw9656 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9656step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9656step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9656 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9656 = injectiveMoment H node2950 := by
  calc
    injectiveMoment H raw9656 = injectiveMoment H raw9656step0 := by
      have heq : raw9656step0 = -raw9656 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9656).symm
    injectiveMoment H raw9656step0 = injectiveMoment H raw9656step1 := by
      have heq : raw9656step1 = (fun i j => raw9656step0 (permutation351 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9656step0 permutation351 permutation23
    _ = injectiveMoment H node2950 := by rfl

def raw9657 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9657step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9657 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9657 = injectiveMoment H node3264 := by
  calc
    injectiveMoment H raw9657 = injectiveMoment H raw9657step0 := by
      have heq : raw9657step0 = (fun i j => raw9657 (permutation276 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9657 permutation276 permutation9
    _ = injectiveMoment H node3264 := by rfl

def raw9658 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9658step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9658 = injectiveMoment H node2946 := by
  calc
    injectiveMoment H raw9658 = injectiveMoment H raw9658step0 := by
      have heq : raw9658step0 = (fun i j => raw9658 (permutation262 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9658 permutation262 permutation11
    _ = injectiveMoment H node2946 := by rfl

def raw9659 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 1, -2]]

def raw9659step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -1, 2]]

def raw9659step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9659 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9659 = injectiveMoment H node3390 := by
  calc
    injectiveMoment H raw9659 = injectiveMoment H raw9659step0 := by
      have heq : raw9659step0 = -raw9659 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9659).symm
    injectiveMoment H raw9659step0 = injectiveMoment H raw9659step1 := by
      have heq : raw9659step1 = (fun i j => raw9659step0 (permutation352 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9659step0 permutation352 permutation23
    _ = injectiveMoment H node3390 := by rfl

def raw9660 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -2, 3], ![0, 0, 3, -3]]

def raw9660step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9660 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9660 = injectiveMoment H node3239 := by
  calc
    injectiveMoment H raw9660 = injectiveMoment H raw9660step0 := by
      have heq : raw9660step0 = (fun i j => raw9660 (permutation275 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9660 permutation275 permutation9
    _ = injectiveMoment H node3239 := by rfl

def raw9661 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 2, -2]]

def raw9661step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9661 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9661 = injectiveMoment H node3034 := by
  calc
    injectiveMoment H raw9661 = injectiveMoment H raw9661step0 := by
      have heq : raw9661step0 = (fun i j => raw9661 (permutation262 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9661 permutation262 permutation11
    _ = injectiveMoment H node3034 := by rfl

def raw9662 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9662step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical9662 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9662 = injectiveMoment H node3283 := by
  calc
    injectiveMoment H raw9662 = injectiveMoment H raw9662step0 := by
      have heq : raw9662step0 = (fun i j => raw9662 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9662 permutation294 permutation9
    _ = injectiveMoment H node3283 := by rfl

def raw9663 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9663step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

theorem canonical9663 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9663 = injectiveMoment H node3384 := by
  calc
    injectiveMoment H raw9663 = injectiveMoment H raw9663step0 := by
      have heq : raw9663step0 = (fun i j => raw9663 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9663 permutation285 permutation15
    _ = injectiveMoment H node3384 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
