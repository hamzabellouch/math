import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8480 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -1, 2]]

def raw8480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8480 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8480 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw8480 = injectiveMoment H raw8480step0 := by
      have hz : ∀ i, raw8480 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8480step0 = (fun i j => raw8480 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8480 permutation9 hz
    injectiveMoment H raw8480step0 = injectiveMoment H raw8480step1 := by
      have heq : raw8480step1 = (fun i j => raw8480step0 (permutation131 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8480step0 permutation131 permutation5
    _ = injectiveMoment H node1151 := by rfl

def raw8481 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![0, -1, 2, -1]]

def raw8481step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -1, 1], ![0, -2, 3, -1], ![0, 1, -2, 1]]

def raw8481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-2, 3, -1], ![1, -2, 1]]

def raw8481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8481 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8481 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw8481 = injectiveMoment H raw8481step0 := by
      have heq : raw8481step0 = -raw8481 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8481).symm
    injectiveMoment H raw8481step0 = injectiveMoment H raw8481step1 := by
      have hz : ∀ i, raw8481step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8481step1 = (fun i j => raw8481step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8481step0 permutation9 hz
    injectiveMoment H raw8481step1 = injectiveMoment H raw8481step2 := by
      have heq : raw8481step2 = (fun i j => raw8481step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8481step1 permutation23 permutation4
    _ = injectiveMoment H node181 := by rfl

def raw8482 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -1, 2]]

def raw8482step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw8482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8482 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8482 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw8482 = injectiveMoment H raw8482step0 := by
      have hz : ∀ i, raw8482 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8482step0 = (fun i j => raw8482 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8482 permutation9 hz
    injectiveMoment H raw8482step0 = injectiveMoment H raw8482step1 := by
      have heq : raw8482step1 = (fun i j => raw8482step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8482step0 permutation28 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw8483 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, -1, -2, 3]]

def raw8483step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 1, -3], ![-1, -2, 3]]

def raw8483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8483 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8483 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw8483 = injectiveMoment H raw8483step0 := by
      have hz : ∀ i, raw8483 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8483step0 = (fun i j => raw8483 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8483 permutation9 hz
    injectiveMoment H raw8483step0 = injectiveMoment H raw8483step1 := by
      have heq : raw8483step1 = (fun i j => raw8483step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8483step0 permutation27 permutation5
    _ = injectiveMoment H node174 := by rfl

def raw8484 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 1, -2, 2], ![1, 0, 0, -1]]

def raw8484step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![1, -1, 2, -2], ![-1, 0, 0, 1]]

def raw8484step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical8484 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8484 = injectiveMoment H node1284 := by
  calc
    injectiveMoment H raw8484 = injectiveMoment H raw8484step0 := by
      have heq : raw8484step0 = -raw8484 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8484).symm
    injectiveMoment H raw8484step0 = injectiveMoment H raw8484step1 := by
      have heq : raw8484step1 = (fun i j => raw8484step0 (permutation29 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8484step0 permutation29 permutation9
    _ = injectiveMoment H node1284 := by rfl

def raw8485 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![1, 0, -1, 0]]

def raw8485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 1, 0], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw8485step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical8485 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8485 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw8485 = injectiveMoment H raw8485step0 := by
      have heq : raw8485step0 = raw8485.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8485).symm
    injectiveMoment H raw8485step0 = injectiveMoment H raw8485step1 := by
      have heq : raw8485step1 = (fun i j => raw8485step0 (permutation24 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8485step0 permutation24 permutation28
    _ = injectiveMoment H node1242 := by rfl

def raw8486 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8486step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

theorem canonical8486 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8486 = injectiveMoment H node2821 := by
  calc
    injectiveMoment H raw8486 = injectiveMoment H raw8486step0 := by
      have heq : raw8486step0 = (fun i j => raw8486 (permutation82 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8486 permutation82 permutation11
    _ = injectiveMoment H node2821 := by rfl

def raw8487 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, -3, 2], ![1, -1, 1, -1]]

def raw8487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -2, 2, -1]]

def raw8487step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical8487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8487 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw8487 = injectiveMoment H raw8487step0 := by
      have heq : raw8487step0 = raw8487.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8487).symm
    injectiveMoment H raw8487step0 = injectiveMoment H raw8487step1 := by
      have heq : raw8487step1 = (fun i j => raw8487step0 (permutation15 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8487step0 permutation15 permutation13
    _ = injectiveMoment H node1083 := by rfl

def raw8488 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, -1, 0], ![1, -1, -1, 1]]

def raw8488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -2, 0, 1]]

def raw8488step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -2, 1, 1], ![-1, 2, 0, -1]]

def raw8488step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical8488 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8488 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw8488 = injectiveMoment H raw8488step0 := by
      have heq : raw8488step0 = raw8488.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8488).symm
    injectiveMoment H raw8488step0 = injectiveMoment H raw8488step1 := by
      have heq : raw8488step1 = -raw8488step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8488step0).symm
    injectiveMoment H raw8488step1 = injectiveMoment H raw8488step2 := by
      have heq : raw8488step2 = (fun i j => raw8488step1 (permutation28 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8488step1 permutation28 permutation14
    _ = injectiveMoment H node1000 := by rfl

def raw8489 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8489step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

theorem canonical8489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8489 = injectiveMoment H node1316 := by
  calc
    injectiveMoment H raw8489 = injectiveMoment H raw8489step0 := by
      have heq : raw8489step0 = (fun i j => raw8489 (permutation21 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8489 permutation21 permutation11
    _ = injectiveMoment H node1316 := by rfl

def raw8490 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -1, -3, 3]]

def raw8490step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw8490step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

theorem canonical8490 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8490 = injectiveMoment H node1317 := by
  calc
    injectiveMoment H raw8490 = injectiveMoment H raw8490step0 := by
      have heq : raw8490step0 = raw8490.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8490).symm
    injectiveMoment H raw8490step0 = injectiveMoment H raw8490step1 := by
      have heq : raw8490step1 = (fun i j => raw8490step0 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8490step0 permutation15 permutation9
    _ = injectiveMoment H node1317 := by rfl

def raw8491 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1]]

def raw8491step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1]]

def raw8491step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 2, -1]]

def raw8491step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8491 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8491 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8491 = injectiveMoment H raw8491step0 := by
      have heq : raw8491step0 = -raw8491 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8491).symm
    injectiveMoment H raw8491step0 = injectiveMoment H raw8491step1 := by
      have hz : ∀ i, raw8491step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8491step1 = (fun i j => raw8491step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8491step0 permutation9 hz
    injectiveMoment H raw8491step1 = injectiveMoment H raw8491step2 := by
      have heq : raw8491step2 = (fun i j => raw8491step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8491step1 permutation8 permutation4
    _ = injectiveMoment H node62 := by rfl

def raw8492 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 0, 0, 0]]

def raw8492step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![0, 0, 0, 0]]

def raw8492step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1]]

def raw8492step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 2, -1]]

def raw8492step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8492 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8492 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8492 = injectiveMoment H raw8492step0 := by
      have heq : raw8492step0 = -raw8492 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8492).symm
    injectiveMoment H raw8492step0 = injectiveMoment H raw8492step1 := by
      have hz : ∀ j, raw8492step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8492step1 = (fun i j => raw8492step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8492step0 permutation27 hz
    injectiveMoment H raw8492step1 = injectiveMoment H raw8492step2 := by
      have hz : ∀ i, raw8492step1 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8492step2 = (fun i j => raw8492step1 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8492step1 permutation9 hz
    injectiveMoment H raw8492step2 = injectiveMoment H raw8492step3 := by
      have heq : raw8492step3 = (fun i j => raw8492step2 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8492step2 permutation8 permutation4
    _ = injectiveMoment H node62 := by rfl

def raw8493 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, -1, 1]]

def raw8493step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1]]

def raw8493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8493 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8493 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw8493 = injectiveMoment H raw8493step0 := by
      have hz : ∀ i, raw8493 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8493step0 = (fun i j => raw8493 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8493 permutation9 hz
    injectiveMoment H raw8493step0 = injectiveMoment H raw8493step1 := by
      have heq : raw8493step1 = (fun i j => raw8493step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8493step0 permutation13 permutation3
    _ = injectiveMoment H node294 := by rfl

def raw8494 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -1, -2, 2]]

def raw8494step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

theorem canonical8494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8494 = injectiveMoment H node2821 := by
  calc
    injectiveMoment H raw8494 = injectiveMoment H raw8494step0 := by
      have heq : raw8494step0 = (fun i j => raw8494 (permutation106 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8494 permutation106 permutation11
    _ = injectiveMoment H node2821 := by rfl

def raw8495 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -2, 3]]

def raw8495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3]]

def raw8495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical8495 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8495 = injectiveMoment H node555 := by
  calc
    injectiveMoment H raw8495 = injectiveMoment H raw8495step0 := by
      have hz : ∀ i, raw8495 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8495step0 = (fun i j => raw8495 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8495 permutation9 hz
    injectiveMoment H raw8495step0 = injectiveMoment H raw8495step1 := by
      have heq : raw8495step1 = (fun i j => raw8495step0 (permutation131 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8495step0 permutation131 permutation5
    _ = injectiveMoment H node555 := by rfl

def raw8496 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![0, -1, 1, 0]]

def raw8496step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -2, 3, -1], ![0, 1, -1, 0]]

def raw8496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 3, -1], ![1, -1, 0]]

def raw8496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8496 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8496 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw8496 = injectiveMoment H raw8496step0 := by
      have heq : raw8496step0 = -raw8496 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8496).symm
    injectiveMoment H raw8496step0 = injectiveMoment H raw8496step1 := by
      have hz : ∀ i, raw8496step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8496step1 = (fun i j => raw8496step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8496step0 permutation9 hz
    injectiveMoment H raw8496step1 = injectiveMoment H raw8496step2 := by
      have heq : raw8496step2 = (fun i j => raw8496step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8496step1 permutation23 permutation4
    _ = injectiveMoment H node185 := by rfl

def raw8497 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![0, -1, -1, 2]]

def raw8497step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -2, 1, 1], ![0, 1, 1, -2]]

def raw8497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![1, 1, -2]]

def raw8497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical8497 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8497 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw8497 = injectiveMoment H raw8497step0 := by
      have heq : raw8497step0 = -raw8497 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8497).symm
    injectiveMoment H raw8497step0 = injectiveMoment H raw8497step1 := by
      have hz : ∀ i, raw8497step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8497step1 = (fun i j => raw8497step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8497step0 permutation9 hz
    injectiveMoment H raw8497step1 = injectiveMoment H raw8497step2 := by
      have heq : raw8497step2 = (fun i j => raw8497step1 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8497step1 permutation15 permutation5
    _ = injectiveMoment H node210 := by rfl

def raw8498 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8498step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, 0, -2], ![-1, -2, 3]]

def raw8498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8498 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw8498 = injectiveMoment H raw8498step0 := by
      have hz : ∀ i, raw8498 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8498step0 = (fun i j => raw8498 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8498 permutation9 hz
    injectiveMoment H raw8498step0 = injectiveMoment H raw8498step1 := by
      have heq : raw8498step1 = (fun i j => raw8498step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8498step0 permutation28 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw8499 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![-1, 2, -3, 2], ![1, -1, 0, 0]]

def raw8499step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 3, -3, 0], ![1, -3, 2, 0]]

def raw8499step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

theorem canonical8499 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8499 = injectiveMoment H node1062 := by
  calc
    injectiveMoment H raw8499 = injectiveMoment H raw8499step0 := by
      have heq : raw8499step0 = raw8499.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8499).symm
    injectiveMoment H raw8499step0 = injectiveMoment H raw8499step1 := by
      have heq : raw8499step1 = (fun i j => raw8499step0 (permutation18 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8499step0 permutation18 permutation27
    _ = injectiveMoment H node1062 := by rfl

def raw8500 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![-1, 2, -2, 1], ![1, -1, -1, 1]]

def raw8500step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 3, -2, -1], ![1, -3, 1, 1]]

def raw8500step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -3, 2, 1], ![-1, 3, -1, -1]]

def raw8500step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical8500 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8500 = injectiveMoment H node937 := by
  calc
    injectiveMoment H raw8500 = injectiveMoment H raw8500step0 := by
      have heq : raw8500step0 = raw8500.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8500).symm
    injectiveMoment H raw8500step0 = injectiveMoment H raw8500step1 := by
      have heq : raw8500step1 = -raw8500step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8500step0).symm
    injectiveMoment H raw8500step1 = injectiveMoment H raw8500step2 := by
      have heq : raw8500step2 = (fun i j => raw8500step1 (permutation28 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8500step1 permutation28 permutation14
    _ = injectiveMoment H node937 := by rfl

def raw8501 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 1, -3, 2]]

def raw8501step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -3, 3], ![0, -1, 3, -2]]

def raw8501step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2]]

def raw8501step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical8501 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8501 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw8501 = injectiveMoment H raw8501step0 := by
      have heq : raw8501step0 = -raw8501 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8501).symm
    injectiveMoment H raw8501step0 = injectiveMoment H raw8501step1 := by
      have hz : ∀ i, raw8501step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8501step1 = (fun i j => raw8501step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8501step0 permutation9 hz
    injectiveMoment H raw8501step1 = injectiveMoment H raw8501step2 := by
      have heq : raw8501step2 = (fun i j => raw8501step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8501step1 permutation8 permutation4
    _ = injectiveMoment H node58 := by rfl

def raw8502 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -3, 1], ![0, -1, 0, 1]]

def raw8502step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -3, 3], ![0, -2, 3, -1], ![0, 1, 0, -1]]

def raw8502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 3, -1], ![1, 0, -1]]

def raw8502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8502 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8502 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw8502 = injectiveMoment H raw8502step0 := by
      have heq : raw8502step0 = -raw8502 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8502).symm
    injectiveMoment H raw8502step0 = injectiveMoment H raw8502step1 := by
      have hz : ∀ i, raw8502step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8502step1 = (fun i j => raw8502step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8502step0 permutation9 hz
    injectiveMoment H raw8502step1 = injectiveMoment H raw8502step2 := by
      have heq : raw8502step2 = (fun i j => raw8502step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8502step1 permutation23 permutation4
    _ = injectiveMoment H node188 := by rfl

def raw8503 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![0, -1, -1, 2]]

def raw8503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -3, 3], ![0, -2, 2, 0], ![0, 1, 1, -2]]

def raw8503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 2, 0], ![1, 1, -2]]

def raw8503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical8503 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8503 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw8503 = injectiveMoment H raw8503step0 := by
      have heq : raw8503step0 = -raw8503 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8503).symm
    injectiveMoment H raw8503step0 = injectiveMoment H raw8503step1 := by
      have hz : ∀ i, raw8503step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8503step1 = (fun i j => raw8503step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8503step0 permutation9 hz
    injectiveMoment H raw8503step1 = injectiveMoment H raw8503step2 := by
      have heq : raw8503step2 = (fun i j => raw8503step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8503step1 permutation24 permutation4
    _ = injectiveMoment H node215 := by rfl

def raw8504 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![-1, 1, 2, -2], ![1, -1, 1, -1]]

def raw8504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, -3, 2, 1], ![1, 2, -2, -1]]

def raw8504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical8504 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8504 = injectiveMoment H node1122 := by
  calc
    injectiveMoment H raw8504 = injectiveMoment H raw8504step0 := by
      have heq : raw8504step0 = raw8504.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8504).symm
    injectiveMoment H raw8504step0 = injectiveMoment H raw8504step1 := by
      have heq : raw8504step1 = (fun i j => raw8504step0 (permutation17 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8504step0 permutation17 permutation13
    _ = injectiveMoment H node1122 := by rfl

def raw8505 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![-1, 1, 3, -3], ![1, -1, 0, 0]]

def raw8505step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, -3, 3, 0], ![1, 2, -3, 0]]

def raw8505step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical8505 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8505 = injectiveMoment H node1103 := by
  calc
    injectiveMoment H raw8505 = injectiveMoment H raw8505step0 := by
      have heq : raw8505step0 = raw8505.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8505).symm
    injectiveMoment H raw8505step0 = injectiveMoment H raw8505step1 := by
      have heq : raw8505step1 = (fun i j => raw8505step0 (permutation17 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8505step0 permutation17 permutation13
    _ = injectiveMoment H node1103 := by rfl

def raw8506 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![0, -1, 1, 0]]

def raw8506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, 3, -2], ![0, -1, -2, 3], ![0, 1, -1, 0]]

def raw8506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw8506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8506 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8506 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw8506 = injectiveMoment H raw8506step0 := by
      have heq : raw8506step0 = -raw8506 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8506).symm
    injectiveMoment H raw8506step0 = injectiveMoment H raw8506step1 := by
      have hz : ∀ i, raw8506step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8506step1 = (fun i j => raw8506step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8506step0 permutation9 hz
    injectiveMoment H raw8506step1 = injectiveMoment H raw8506step2 := by
      have heq : raw8506step2 = (fun i j => raw8506step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8506step1 permutation24 permutation3
    _ = injectiveMoment H node263 := by rfl

def raw8507 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![0, -1, 0, 1]]

def raw8507step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1]]

def raw8507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -3, 4], ![1, 0, -1]]

def raw8507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8507 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8507 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw8507 = injectiveMoment H raw8507step0 := by
      have heq : raw8507step0 = -raw8507 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8507).symm
    injectiveMoment H raw8507step0 = injectiveMoment H raw8507step1 := by
      have hz : ∀ i, raw8507step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8507step1 = (fun i j => raw8507step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8507step0 permutation9 hz
    injectiveMoment H raw8507step1 = injectiveMoment H raw8507step2 := by
      have heq : raw8507step2 = (fun i j => raw8507step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8507step1 permutation23 permutation3
    _ = injectiveMoment H node248 := by rfl

def raw8508 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, -1, -1, 1]]

def raw8508step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![1, 0, -2, 1]]

def raw8508step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![0, 1, -2, 1], ![-1, 0, 2, -1]]

def raw8508step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical8508 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8508 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw8508 = injectiveMoment H raw8508step0 := by
      have heq : raw8508step0 = raw8508.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8508).symm
    injectiveMoment H raw8508step0 = injectiveMoment H raw8508step1 := by
      have heq : raw8508step1 = -raw8508step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8508step0).symm
    injectiveMoment H raw8508step1 = injectiveMoment H raw8508step2 := by
      have heq : raw8508step2 = (fun i j => raw8508step1 (permutation28 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8508step1 permutation28 permutation10
    _ = injectiveMoment H node1260 := by rfl

def raw8509 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8509step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical8509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8509 = injectiveMoment H node3424 := by
  calc
    injectiveMoment H raw8509 = injectiveMoment H raw8509step0 := by
      have heq : raw8509step0 = (fun i j => raw8509 (permutation189 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8509 permutation189 permutation15
    _ = injectiveMoment H node3424 := by rfl

def raw8510 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8510step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem canonical8510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8510 = injectiveMoment H node3162 := by
  calc
    injectiveMoment H raw8510 = injectiveMoment H raw8510step0 := by
      have heq : raw8510step0 = (fun i j => raw8510 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8510 permutation258 permutation9
    _ = injectiveMoment H node3162 := by rfl

def raw8511 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![1, 0, 3, -4]]

def raw8511step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

theorem canonical8511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8511 = injectiveMoment H node2953 := by
  calc
    injectiveMoment H raw8511 = injectiveMoment H raw8511step0 := by
      have heq : raw8511step0 = (fun i j => raw8511 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8511 permutation258 permutation9
    _ = injectiveMoment H node2953 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
