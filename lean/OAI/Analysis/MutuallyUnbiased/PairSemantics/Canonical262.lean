import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8384 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8384step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8384 = injectiveMoment H node3194 := by
  calc
    injectiveMoment H raw8384 = injectiveMoment H raw8384step0 := by
      have heq : raw8384step0 = (fun i j => raw8384 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8384 permutation277 permutation9
    _ = injectiveMoment H node3194 := by rfl

def raw8385 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8385step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

theorem canonical8385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8385 = injectiveMoment H node3269 := by
  calc
    injectiveMoment H raw8385 = injectiveMoment H raw8385step0 := by
      have heq : raw8385step0 = (fun i j => raw8385 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8385 permutation277 permutation9
    _ = injectiveMoment H node3269 := by rfl

def raw8386 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 2, 1, -3]]

def raw8386step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -2, -1, 3]]

def raw8386step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8386step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical8386 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8386 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw8386 = injectiveMoment H raw8386step0 := by
      have heq : raw8386step0 = -raw8386 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8386).symm
    injectiveMoment H raw8386step0 = injectiveMoment H raw8386step1 := by
      have hz : ∀ i, raw8386step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8386step1 = (fun i j => raw8386step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8386step0 permutation9 hz
    injectiveMoment H raw8386step1 = injectiveMoment H raw8386step2 := by
      have heq : raw8386step2 = (fun i j => raw8386step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8386step1 permutation7 permutation5
    _ = injectiveMoment H node56 := by rfl

def raw8387 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8387step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8387step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical8387 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8387 = injectiveMoment H node3107 := by
  calc
    injectiveMoment H raw8387 = injectiveMoment H raw8387step0 := by
      have heq : raw8387step0 = -raw8387 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8387).symm
    injectiveMoment H raw8387step0 = injectiveMoment H raw8387step1 := by
      have heq : raw8387step1 = (fun i j => raw8387step0 (permutation366 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8387step0 permutation366 permutation15
    _ = injectiveMoment H node3107 := by rfl

def raw8388 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8388step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical8388 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8388 = injectiveMoment H node3270 := by
  calc
    injectiveMoment H raw8388 = injectiveMoment H raw8388step0 := by
      have heq : raw8388step0 = (fun i j => raw8388 (permutation279 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8388 permutation279 permutation9
    _ = injectiveMoment H node3270 := by rfl

def raw8389 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8389step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical8389 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8389 = injectiveMoment H node2596 := by
  calc
    injectiveMoment H raw8389 = injectiveMoment H raw8389step0 := by
      have heq : raw8389step0 = (fun i j => raw8389 (permutation80 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8389 permutation80 permutation11
    _ = injectiveMoment H node2596 := by rfl

def raw8390 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical8390 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8390 = injectiveMoment H node2640 := by
  calc
    injectiveMoment H raw8390 = injectiveMoment H raw8390step0 := by
      have heq : raw8390step0 = (fun i j => raw8390 (permutation80 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8390 permutation80 permutation11
    _ = injectiveMoment H node2640 := by rfl

def raw8391 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 2, 2, -3], ![1, 0, -2, 1]]

def raw8391step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 0, 2, -2], ![1, 1, -3, 1]]

def raw8391step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 1, -2, 0], ![0, 0, -2, 2], ![-1, -1, 3, -1]]

def raw8391step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical8391 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8391 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw8391 = injectiveMoment H raw8391step0 := by
      have heq : raw8391step0 = raw8391.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8391).symm
    injectiveMoment H raw8391step0 = injectiveMoment H raw8391step1 := by
      have heq : raw8391step1 = -raw8391step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8391step0).symm
    injectiveMoment H raw8391step1 = injectiveMoment H raw8391step2 := by
      have heq : raw8391step2 = (fun i j => raw8391step1 (permutation28 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8391step1 permutation28 permutation10
    _ = injectiveMoment H node959 := by rfl

def raw8392 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8392step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -2, -2, 3], ![-1, 0, 1, 0]]

def raw8392step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical8392 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8392 = injectiveMoment H node2823 := by
  calc
    injectiveMoment H raw8392 = injectiveMoment H raw8392step0 := by
      have heq : raw8392step0 = -raw8392 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8392).symm
    injectiveMoment H raw8392step0 = injectiveMoment H raw8392step1 := by
      have heq : raw8392step1 = (fun i j => raw8392step0 (permutation139 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8392step0 permutation139 permutation9
    _ = injectiveMoment H node2823 := by rfl

def raw8393 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8393step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8393 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8393 = injectiveMoment H node441 := by
  calc
    injectiveMoment H raw8393 = injectiveMoment H raw8393step0 := by
      have heq : raw8393step0 = -raw8393 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8393).symm
    injectiveMoment H raw8393step0 = injectiveMoment H raw8393step1 := by
      have hz : ∀ i, raw8393step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8393step1 = (fun i j => raw8393step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8393step0 permutation9 hz
    injectiveMoment H raw8393step1 = injectiveMoment H raw8393step2 := by
      have heq : raw8393step2 = (fun i j => raw8393step1 (permutation120 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8393step1 permutation120 permutation3
    _ = injectiveMoment H node441 := by rfl

def raw8394 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8394step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical8394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8394 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw8394 = injectiveMoment H raw8394step0 := by
      have heq : raw8394step0 = (fun i j => raw8394 (permutation116 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8394 permutation116 permutation13
    _ = injectiveMoment H node2448 := by rfl

def raw8395 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, -1, 1]]

def raw8395step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1]]

def raw8395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1]]

def raw8395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8395 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8395 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw8395 = injectiveMoment H raw8395step0 := by
      have heq : raw8395step0 = -raw8395 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8395).symm
    injectiveMoment H raw8395step0 = injectiveMoment H raw8395step1 := by
      have hz : ∀ i, raw8395step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8395step1 = (fun i j => raw8395step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8395step0 permutation9 hz
    injectiveMoment H raw8395step1 = injectiveMoment H raw8395step2 := by
      have heq : raw8395step2 = (fun i j => raw8395step1 (permutation104 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8395step1 permutation104 permutation5
    _ = injectiveMoment H node570 := by rfl

def raw8396 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8396step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8396 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8396 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw8396 = injectiveMoment H raw8396step0 := by
      have heq : raw8396step0 = -raw8396 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8396).symm
    injectiveMoment H raw8396step0 = injectiveMoment H raw8396step1 := by
      have hz : ∀ i, raw8396step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8396step1 = (fun i j => raw8396step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8396step0 permutation9 hz
    injectiveMoment H raw8396step1 = injectiveMoment H raw8396step2 := by
      have heq : raw8396step2 = (fun i j => raw8396step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8396step1 permutation21 permutation5
    _ = injectiveMoment H node271 := by rfl

def raw8397 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![0, 0, -2, 2]]

def raw8397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -2, 4], ![0, 0, 2, -2]]

def raw8397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-2, -2, 4], ![0, 2, -2]]

def raw8397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical8397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8397 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw8397 = injectiveMoment H raw8397step0 := by
      have heq : raw8397step0 = -raw8397 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8397).symm
    injectiveMoment H raw8397step0 = injectiveMoment H raw8397step1 := by
      have hz : ∀ i, raw8397step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8397step1 = (fun i j => raw8397step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8397step0 permutation9 hz
    injectiveMoment H raw8397step1 = injectiveMoment H raw8397step2 := by
      have heq : raw8397step2 = (fun i j => raw8397step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8397step1 permutation21 permutation5
    _ = injectiveMoment H node145 := by rfl

def raw8398 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical8398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8398 = injectiveMoment H node2605 := by
  calc
    injectiveMoment H raw8398 = injectiveMoment H raw8398step0 := by
      have heq : raw8398step0 = (fun i j => raw8398 (permutation80 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8398 permutation80 permutation11
    _ = injectiveMoment H node2605 := by rfl

def raw8399 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8399step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical8399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8399 = injectiveMoment H node2645 := by
  calc
    injectiveMoment H raw8399 = injectiveMoment H raw8399step0 := by
      have heq : raw8399step0 = (fun i j => raw8399 (permutation80 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8399 permutation80 permutation11
    _ = injectiveMoment H node2645 := by rfl

def raw8400 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw8400step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw8400step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical8400 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8400 = injectiveMoment H node3343 := by
  calc
    injectiveMoment H raw8400 = injectiveMoment H raw8400step0 := by
      have heq : raw8400step0 = -raw8400 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8400).symm
    injectiveMoment H raw8400step0 = injectiveMoment H raw8400step1 := by
      have heq : raw8400step1 = (fun i j => raw8400step0 (permutation377 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8400step0 permutation377 permutation9
    _ = injectiveMoment H node3343 := by rfl

def raw8401 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 2, 1, -2], ![1, 0, -2, 1]]

def raw8401step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw8401step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical8401 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8401 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw8401 = injectiveMoment H raw8401step0 := by
      have heq : raw8401step0 = raw8401.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8401).symm
    injectiveMoment H raw8401step0 = injectiveMoment H raw8401step1 := by
      have heq : raw8401step1 = (fun i j => raw8401step0 (permutation15 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8401step0 permutation15 permutation10
    _ = injectiveMoment H node1047 := by rfl

def raw8402 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 2, 2, -3], ![1, 0, -3, 2]]

def raw8402step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 1, 2, -3], ![1, 0, -3, 2]]

def raw8402step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

theorem canonical8402 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8402 = injectiveMoment H node1046 := by
  calc
    injectiveMoment H raw8402 = injectiveMoment H raw8402step0 := by
      have heq : raw8402step0 = raw8402.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8402).symm
    injectiveMoment H raw8402step0 = injectiveMoment H raw8402step1 := by
      have heq : raw8402step1 = (fun i j => raw8402step0 (permutation15 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8402step0 permutation15 permutation10
    _ = injectiveMoment H node1046 := by rfl

def raw8403 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8403step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical8403 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8403 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw8403 = injectiveMoment H raw8403step0 := by
      have heq : raw8403step0 = (fun i j => raw8403 (permutation112 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8403 permutation112 permutation14
    _ = injectiveMoment H node2449 := by rfl

def raw8404 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8404step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8404 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8404 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw8404 = injectiveMoment H raw8404step0 := by
      have heq : raw8404step0 = -raw8404 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8404).symm
    injectiveMoment H raw8404step0 = injectiveMoment H raw8404step1 := by
      have hz : ∀ i, raw8404step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8404step1 = (fun i j => raw8404step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8404step0 permutation9 hz
    injectiveMoment H raw8404step1 = injectiveMoment H raw8404step2 := by
      have heq : raw8404step2 = (fun i j => raw8404step1 (permutation121 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8404step1 permutation121 permutation3
    _ = injectiveMoment H node570 := by rfl

def raw8405 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, 0, -1, 0]]

def raw8405step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical8405 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8405 = injectiveMoment H node2642 := by
  calc
    injectiveMoment H raw8405 = injectiveMoment H raw8405step0 := by
      have heq : raw8405step0 = (fun i j => raw8405 (permutation112 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8405 permutation112 permutation13
    _ = injectiveMoment H node2642 := by rfl

def raw8406 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw8406step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw8406step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical8406 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8406 = injectiveMoment H node3350 := by
  calc
    injectiveMoment H raw8406 = injectiveMoment H raw8406step0 := by
      have heq : raw8406step0 = -raw8406 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8406).symm
    injectiveMoment H raw8406step0 = injectiveMoment H raw8406step1 := by
      have heq : raw8406step1 = (fun i j => raw8406step0 (permutation364 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8406step0 permutation364 permutation9
    _ = injectiveMoment H node3350 := by rfl

def raw8407 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, -1, 1]]

def raw8407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, -1, 1]]

def raw8407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8407 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8407 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw8407 = injectiveMoment H raw8407step0 := by
      have hz : ∀ i, raw8407 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8407step0 = (fun i j => raw8407 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8407 permutation9 hz
    injectiveMoment H raw8407step0 = injectiveMoment H raw8407step1 := by
      have heq : raw8407step1 = (fun i j => raw8407step0 (permutation112 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8407step0 permutation112 permutation7
    _ = injectiveMoment H node711 := by rfl

def raw8408 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, -1, 3], ![1, 1, 2, -4]]

def raw8408step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8408 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8408 = injectiveMoment H node3124 := by
  calc
    injectiveMoment H raw8408 = injectiveMoment H raw8408step0 := by
      have heq : raw8408step0 = (fun i j => raw8408 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8408 permutation258 permutation9
    _ = injectiveMoment H node3124 := by rfl

def raw8409 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![0, 1, 2, -3]]

def raw8409step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical8409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8409 = injectiveMoment H node3419 := by
  calc
    injectiveMoment H raw8409 = injectiveMoment H raw8409step0 := by
      have heq : raw8409step0 = (fun i j => raw8409 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8409 permutation259 permutation9
    _ = injectiveMoment H node3419 := by rfl

def raw8410 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![0, 0, -2, 2]]

def raw8410step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -2, -1, 3], ![0, 0, 2, -2]]

def raw8410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![0, 2, -2]]

def raw8410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8410 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8410 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw8410 = injectiveMoment H raw8410step0 := by
      have heq : raw8410step0 = -raw8410 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8410).symm
    injectiveMoment H raw8410step0 = injectiveMoment H raw8410step1 := by
      have hz : ∀ i, raw8410step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8410step1 = (fun i j => raw8410step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8410step0 permutation9 hz
    injectiveMoment H raw8410step1 = injectiveMoment H raw8410step2 := by
      have heq : raw8410step2 = (fun i j => raw8410step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8410step1 permutation26 permutation3
    _ = injectiveMoment H node185 := by rfl

def raw8411 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 2, -4], ![0, 0, -3, 3]]

def raw8411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -2, -2, 4], ![0, 0, 3, -3]]

def raw8411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-2, -2, 4], ![0, 3, -3]]

def raw8411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8411 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8411 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw8411 = injectiveMoment H raw8411step0 := by
      have heq : raw8411step0 = -raw8411 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8411).symm
    injectiveMoment H raw8411step0 = injectiveMoment H raw8411step1 := by
      have hz : ∀ i, raw8411step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8411step1 = (fun i j => raw8411step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8411step0 permutation9 hz
    injectiveMoment H raw8411step1 = injectiveMoment H raw8411step2 := by
      have heq : raw8411step2 = (fun i j => raw8411step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8411step1 permutation26 permutation3
    _ = injectiveMoment H node155 := by rfl

def raw8412 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![-1, 2, 0, -1], ![1, 0, -2, 1]]

def raw8412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![-1, 0, 2, -1]]

def raw8412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical8412 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8412 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw8412 = injectiveMoment H raw8412step0 := by
      have heq : raw8412step0 = -raw8412 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8412).symm
    injectiveMoment H raw8412step0 = injectiveMoment H raw8412step1 := by
      have heq : raw8412step1 = (fun i j => raw8412step0 (permutation27 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8412step0 permutation27 permutation13
    _ = injectiveMoment H node1000 := by rfl

def raw8413 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![-1, 2, 1, -2], ![1, 0, -3, 2]]

def raw8413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw8413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

theorem canonical8413 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8413 = injectiveMoment H node1049 := by
  calc
    injectiveMoment H raw8413 = injectiveMoment H raw8413step0 := by
      have heq : raw8413step0 = raw8413.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8413).symm
    injectiveMoment H raw8413step0 = injectiveMoment H raw8413step1 := by
      have heq : raw8413step1 = (fun i j => raw8413step0 (permutation15 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8413step0 permutation15 permutation10
    _ = injectiveMoment H node1049 := by rfl

def raw8414 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, -2, 0]]

def raw8414step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0]]

def raw8414step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8414 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8414 = injectiveMoment H raw8414step0 := by
      have hz : ∀ i, raw8414 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8414step0 = (fun i j => raw8414 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8414 permutation9 hz
    injectiveMoment H raw8414step0 = injectiveMoment H raw8414step1 := by
      have heq : raw8414step1 = (fun i j => raw8414step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8414step0 permutation6 permutation7
    _ = injectiveMoment H node62 := by rfl

def raw8415 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![0, 0, -2, 2]]

def raw8415step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![0, -2, 2]]

def raw8415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8415 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw8415 = injectiveMoment H raw8415step0 := by
      have hz : ∀ i, raw8415 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8415step0 = (fun i j => raw8415 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8415 permutation9 hz
    injectiveMoment H raw8415step0 = injectiveMoment H raw8415step1 := by
      have heq : raw8415step1 = (fun i j => raw8415step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8415step0 permutation28 permutation5
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
