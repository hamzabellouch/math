import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9440 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9440step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9440 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9440 = injectiveMoment H node3167 := by
  calc
    injectiveMoment H raw9440 = injectiveMoment H raw9440step0 := by
      have heq : raw9440step0 = (fun i j => raw9440 (permutation338 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9440 permutation338 permutation14
    _ = injectiveMoment H node3167 := by rfl

def raw9441 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, -1, 4], ![1, 2, 0, -3]]

def raw9441step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem canonical9441 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9441 = injectiveMoment H node2899 := by
  calc
    injectiveMoment H raw9441 = injectiveMoment H raw9441step0 := by
      have heq : raw9441step0 = (fun i j => raw9441 (permutation258 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9441 permutation258 permutation11
    _ = injectiveMoment H node2899 := by rfl

def raw9442 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, -1, -2]]

def raw9442step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

theorem canonical9442 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9442 = injectiveMoment H node2985 := by
  calc
    injectiveMoment H raw9442 = injectiveMoment H raw9442step0 := by
      have heq : raw9442step0 = (fun i j => raw9442 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9442 permutation258 permutation9
    _ = injectiveMoment H node2985 := by rfl

def raw9443 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 2, 0, 0]]

def raw9443step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9443 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9443 = injectiveMoment H node3167 := by
  calc
    injectiveMoment H raw9443 = injectiveMoment H raw9443step0 := by
      have heq : raw9443step0 = (fun i j => raw9443 (permutation337 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9443 permutation337 permutation14
    _ = injectiveMoment H node3167 := by rfl

def raw9444 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, -1, 1]]

def raw9444step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9444 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9444 = injectiveMoment H node3043 := by
  calc
    injectiveMoment H raw9444 = injectiveMoment H raw9444step0 := by
      have heq : raw9444step0 = (fun i j => raw9444 (permutation308 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9444 permutation308 permutation12
    _ = injectiveMoment H node3043 := by rfl

def raw9445 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1]]

def raw9445step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, -1, 0, -1]]

def raw9445step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9445 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9445 = injectiveMoment H node3393 := by
  calc
    injectiveMoment H raw9445 = injectiveMoment H raw9445step0 := by
      have heq : raw9445step0 = -raw9445 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9445).symm
    injectiveMoment H raw9445step0 = injectiveMoment H raw9445step1 := by
      have heq : raw9445step1 = (fun i j => raw9445step0 (permutation326 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9445step0 permutation326 permutation20
    _ = injectiveMoment H node3393 := by rfl

def raw9446 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def raw9446step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical9446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9446 = injectiveMoment H node3180 := by
  calc
    injectiveMoment H raw9446 = injectiveMoment H raw9446step0 := by
      have heq : raw9446step0 = (fun i j => raw9446 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9446 permutation258 permutation9
    _ = injectiveMoment H node3180 := by rfl

def raw9447 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def raw9447step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

theorem canonical9447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9447 = injectiveMoment H node3214 := by
  calc
    injectiveMoment H raw9447 = injectiveMoment H raw9447step0 := by
      have heq : raw9447step0 = (fun i j => raw9447 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9447 permutation258 permutation9
    _ = injectiveMoment H node3214 := by rfl

def raw9448 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9448step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem canonical9448 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9448 = injectiveMoment H node3058 := by
  calc
    injectiveMoment H raw9448 = injectiveMoment H raw9448step0 := by
      have heq : raw9448step0 = (fun i j => raw9448 (permutation333 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9448 permutation333 permutation10
    _ = injectiveMoment H node3058 := by rfl

def raw9449 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9449step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical9449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9449 = injectiveMoment H node3055 := by
  calc
    injectiveMoment H raw9449 = injectiveMoment H raw9449step0 := by
      have heq : raw9449step0 = (fun i j => raw9449 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9449 permutation258 permutation9
    _ = injectiveMoment H node3055 := by rfl

def raw9450 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9450step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9450 = injectiveMoment H node3064 := by
  calc
    injectiveMoment H raw9450 = injectiveMoment H raw9450step0 := by
      have heq : raw9450step0 = (fun i j => raw9450 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9450 permutation331 permutation10
    _ = injectiveMoment H node3064 := by rfl

def raw9451 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0]]

def raw9451step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0]]

def raw9451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical9451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9451 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw9451 = injectiveMoment H raw9451step0 := by
      have hz : ∀ i, raw9451 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9451step0 = (fun i j => raw9451 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9451 permutation9 hz
    injectiveMoment H raw9451step0 = injectiveMoment H raw9451step1 := by
      have heq : raw9451step1 = (fun i j => raw9451step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9451step0 permutation29 permutation4
    _ = injectiveMoment H node293 := by rfl

def raw9452 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def raw9452step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical9452 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9452 = injectiveMoment H node3181 := by
  calc
    injectiveMoment H raw9452 = injectiveMoment H raw9452step0 := by
      have heq : raw9452step0 = (fun i j => raw9452 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9452 permutation258 permutation9
    _ = injectiveMoment H node3181 := by rfl

def raw9453 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def raw9453step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9453 = injectiveMoment H node3096 := by
  calc
    injectiveMoment H raw9453 = injectiveMoment H raw9453step0 := by
      have heq : raw9453step0 = (fun i j => raw9453 (permutation349 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9453 permutation349 permutation19
    _ = injectiveMoment H node3096 := by rfl

def raw9454 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9454step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9454 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9454 = injectiveMoment H node3061 := by
  calc
    injectiveMoment H raw9454 = injectiveMoment H raw9454step0 := by
      have heq : raw9454step0 = (fun i j => raw9454 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9454 permutation331 permutation10
    _ = injectiveMoment H node3061 := by rfl

def raw9455 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9455step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem canonical9455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9455 = injectiveMoment H node2986 := by
  calc
    injectiveMoment H raw9455 = injectiveMoment H raw9455step0 := by
      have heq : raw9455step0 = (fun i j => raw9455 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9455 permutation258 permutation9
    _ = injectiveMoment H node2986 := by rfl

def raw9456 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 2, -2]]

def raw9456step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical9456 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9456 = injectiveMoment H node3131 := by
  calc
    injectiveMoment H raw9456 = injectiveMoment H raw9456step0 := by
      have heq : raw9456step0 = (fun i j => raw9456 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9456 permutation258 permutation9
    _ = injectiveMoment H node3131 := by rfl

def raw9457 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def raw9457step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9457step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9457 = injectiveMoment H node3090 := by
  calc
    injectiveMoment H raw9457 = injectiveMoment H raw9457step0 := by
      have heq : raw9457step0 = -raw9457 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9457).symm
    injectiveMoment H raw9457step0 = injectiveMoment H raw9457step1 := by
      have heq : raw9457step1 = (fun i j => raw9457step0 (permutation345 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9457step0 permutation345 permutation11
    _ = injectiveMoment H node3090 := by rfl

def raw9458 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def raw9458step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0]]

def raw9458step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9458 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9458 = injectiveMoment H node3173 := by
  calc
    injectiveMoment H raw9458 = injectiveMoment H raw9458step0 := by
      have heq : raw9458step0 = -raw9458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9458).symm
    injectiveMoment H raw9458step0 = injectiveMoment H raw9458step1 := by
      have heq : raw9458step1 = (fun i j => raw9458step0 (permutation343 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9458step0 permutation343 permutation12
    _ = injectiveMoment H node3173 := by rfl

def raw9459 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def raw9459step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, -2, 0], ![-2, 2, 1, -1]]

def raw9459step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9459 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9459 = injectiveMoment H node3090 := by
  calc
    injectiveMoment H raw9459 = injectiveMoment H raw9459step0 := by
      have heq : raw9459step0 = -raw9459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9459).symm
    injectiveMoment H raw9459step0 = injectiveMoment H raw9459step1 := by
      have heq : raw9459step1 = (fun i j => raw9459step0 (permutation316 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9459step0 permutation316 permutation13
    _ = injectiveMoment H node3090 := by rfl

def raw9460 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9460step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical9460 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9460 = injectiveMoment H node3057 := by
  calc
    injectiveMoment H raw9460 = injectiveMoment H raw9460step0 := by
      have heq : raw9460step0 = (fun i j => raw9460 (permutation333 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9460 permutation333 permutation10
    _ = injectiveMoment H node3057 := by rfl

def raw9461 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9461step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical9461 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9461 = injectiveMoment H node3057 := by
  calc
    injectiveMoment H raw9461 = injectiveMoment H raw9461step0 := by
      have heq : raw9461step0 = (fun i j => raw9461 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9461 permutation308 permutation9
    _ = injectiveMoment H node3057 := by rfl

def raw9462 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9462step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9462 = injectiveMoment H node2893 := by
  calc
    injectiveMoment H raw9462 = injectiveMoment H raw9462step0 := by
      have heq : raw9462step0 = (fun i j => raw9462 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9462 permutation308 permutation9
    _ = injectiveMoment H node2893 := by rfl

def raw9463 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def raw9463step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9463 = injectiveMoment H node2884 := by
  calc
    injectiveMoment H raw9463 = injectiveMoment H raw9463step0 := by
      have heq : raw9463step0 = (fun i j => raw9463 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9463 permutation308 permutation9
    _ = injectiveMoment H node2884 := by rfl

def raw9464 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw9464step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9464 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9464 = injectiveMoment H node3205 := by
  calc
    injectiveMoment H raw9464 = injectiveMoment H raw9464step0 := by
      have heq : raw9464step0 = (fun i j => raw9464 (permutation338 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9464 permutation338 permutation13
    _ = injectiveMoment H node3205 := by rfl

def raw9465 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9465step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical9465 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9465 = injectiveMoment H node3059 := by
  calc
    injectiveMoment H raw9465 = injectiveMoment H raw9465step0 := by
      have heq : raw9465step0 = (fun i j => raw9465 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9465 permutation258 permutation9
    _ = injectiveMoment H node3059 := by rfl

def raw9466 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9466step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical9466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9466 = injectiveMoment H node3063 := by
  calc
    injectiveMoment H raw9466 = injectiveMoment H raw9466step0 := by
      have heq : raw9466step0 = (fun i j => raw9466 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9466 permutation331 permutation10
    _ = injectiveMoment H node3063 := by rfl

def raw9467 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 1, 1, -3]]

def raw9467step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical9467 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9467 = injectiveMoment H node2987 := by
  calc
    injectiveMoment H raw9467 = injectiveMoment H raw9467step0 := by
      have heq : raw9467step0 = (fun i j => raw9467 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9467 permutation258 permutation9
    _ = injectiveMoment H node2987 := by rfl

def raw9468 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 0, -2]]

def raw9468step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical9468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9468 = injectiveMoment H node3060 := by
  calc
    injectiveMoment H raw9468 = injectiveMoment H raw9468step0 := by
      have heq : raw9468step0 = (fun i j => raw9468 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9468 permutation258 permutation9
    _ = injectiveMoment H node3060 := by rfl

def raw9469 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def raw9469step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9469 = injectiveMoment H node3199 := by
  calc
    injectiveMoment H raw9469 = injectiveMoment H raw9469step0 := by
      have heq : raw9469step0 = (fun i j => raw9469 (permutation283 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9469 permutation283 permutation12
    _ = injectiveMoment H node3199 := by rfl

def raw9470 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def raw9470step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9470 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9470 = injectiveMoment H node3433 := by
  calc
    injectiveMoment H raw9470 = injectiveMoment H raw9470step0 := by
      have heq : raw9470step0 = (fun i j => raw9470 (permutation219 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9470 permutation219 permutation27
    _ = injectiveMoment H node3433 := by rfl

def raw9471 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 1, 1]]

def raw9471step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical9471 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9471 = injectiveMoment H node3442 := by
  calc
    injectiveMoment H raw9471 = injectiveMoment H raw9471step0 := by
      have heq : raw9471step0 = (fun i j => raw9471 (permutation250 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9471 permutation250 permutation20
    _ = injectiveMoment H node3442 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
