import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw7456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7456 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7456 = injectiveMoment H node2468 := by
  calc
    injectiveMoment H raw7456 = injectiveMoment H raw7456step0 := by
      have heq : raw7456step0 = (fun i j => raw7456 (permutation263 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7456 permutation263 permutation4
    _ = injectiveMoment H node2468 := by rfl

def raw7457 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -2, 1]]

def raw7457step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 2, -1]]

def raw7457step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7457 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw7457 = injectiveMoment H raw7457step0 := by
      have heq : raw7457step0 = -raw7457 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7457).symm
    injectiveMoment H raw7457step0 = injectiveMoment H raw7457step1 := by
      have heq : raw7457step1 = (fun i j => raw7457step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7457step0 permutation8 permutation4
    _ = injectiveMoment H node62 := by rfl

def raw7458 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![0, -3, 3], ![1, 0, -1]]

def raw7458step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7458 = injectiveMoment H node289 := by
  calc
    injectiveMoment H raw7458 = injectiveMoment H raw7458step0 := by
      have heq : raw7458step0 = (fun i j => raw7458 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7458 permutation11 permutation3
    _ = injectiveMoment H node289 := by rfl

def raw7459 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![1, -3, 2]]

def raw7459step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2]]

def raw7459step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7459 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7459 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7459 = injectiveMoment H raw7459step0 := by
      have heq : raw7459step0 = -raw7459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7459).symm
    injectiveMoment H raw7459step0 = injectiveMoment H raw7459step1 := by
      have heq : raw7459step1 = (fun i j => raw7459step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7459step0 permutation8 permutation4
    _ = injectiveMoment H node58 := by rfl

def raw7460 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![0, 0, 0]]

def raw7460step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2], ![0, 0, 0]]

def raw7460step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2]]

def raw7460step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7460 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7460 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7460 = injectiveMoment H raw7460step0 := by
      have heq : raw7460step0 = -raw7460 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7460).symm
    injectiveMoment H raw7460step0 = injectiveMoment H raw7460step1 := by
      have hz : ∀ j, raw7460step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7460step1 = (fun i j => raw7460step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7460step0 permutation27 hz
    injectiveMoment H raw7460step1 = injectiveMoment H raw7460step2 := by
      have heq : raw7460step2 = (fun i j => raw7460step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7460step1 permutation8 permutation4
    _ = injectiveMoment H node58 := by rfl

def raw7461 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 4, -4], ![1, -4, 3]]

def raw7461step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -4, 4], ![-1, 4, -3]]

def raw7461step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7461 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7461 = injectiveMoment H node54 := by
  calc
    injectiveMoment H raw7461 = injectiveMoment H raw7461step0 := by
      have heq : raw7461step0 = -raw7461 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7461).symm
    injectiveMoment H raw7461step0 = injectiveMoment H raw7461step1 := by
      have heq : raw7461step1 = (fun i j => raw7461step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7461step0 permutation8 permutation4
    _ = injectiveMoment H node54 := by rfl

def raw7462 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1]]

def raw7462step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical7462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7462 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7462 = injectiveMoment H raw7462step0 := by
      have hz : ∀ i, raw7462 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7462step0 = (fun i j => raw7462 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7462 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

def raw7463 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-4, 2, 1, 1], ![5, -2, -2, -1]]

def raw7463step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 1, -2], ![0, 1, -1]]

def raw7463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical7463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7463 = injectiveMoment H node238 := by
  calc
    injectiveMoment H raw7463 = injectiveMoment H raw7463step0 := by
      have heq : raw7463step0 = raw7463.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7463).symm
    injectiveMoment H raw7463step0 = injectiveMoment H raw7463step1 := by
      have heq : raw7463step1 = (fun i j => raw7463step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7463step0 permutation13 permutation3
    _ = injectiveMoment H node238 := by rfl

def raw7464 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-3, 2, -2, 3], ![4, -2, 1, -3]]

def raw7464step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, -2, 1], ![0, 3, -3]]

def raw7464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical7464 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7464 = injectiveMoment H node257 := by
  calc
    injectiveMoment H raw7464 = injectiveMoment H raw7464step0 := by
      have heq : raw7464step0 = raw7464.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7464).symm
    injectiveMoment H raw7464step0 = injectiveMoment H raw7464step1 := by
      have heq : raw7464step1 = (fun i j => raw7464step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7464step0 permutation10 permutation3
    _ = injectiveMoment H node257 := by rfl

def raw7465 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-3, 3, -2, 2], ![4, -3, 1, -2]]

def raw7465step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, -2, 1], ![0, 2, -2]]

def raw7465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical7465 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7465 = injectiveMoment H node257 := by
  calc
    injectiveMoment H raw7465 = injectiveMoment H raw7465step0 := by
      have heq : raw7465step0 = raw7465.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7465).symm
    injectiveMoment H raw7465step0 = injectiveMoment H raw7465step1 := by
      have heq : raw7465step1 = (fun i j => raw7465step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7465step0 permutation13 permutation3
    _ = injectiveMoment H node257 := by rfl

def raw7466 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-3, 3, 1, -1], ![4, -3, -2, 1]]

def raw7466step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 1, -2], ![0, -1, 1]]

def raw7466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 3, -3], ![1, 1, -2]]

theorem canonical7466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7466 = injectiveMoment H node251 := by
  calc
    injectiveMoment H raw7466 = injectiveMoment H raw7466step0 := by
      have heq : raw7466step0 = raw7466.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7466).symm
    injectiveMoment H raw7466step0 = injectiveMoment H raw7466step1 := by
      have heq : raw7466step1 = (fun i j => raw7466step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7466step0 permutation13 permutation3
    _ = injectiveMoment H node251 := by rfl

def raw7467 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, -2, 1, 3], ![3, 2, -2, -3]]

def raw7467step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![1, 1, -2], ![0, 3, -3]]

def raw7467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

theorem canonical7467 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7467 = injectiveMoment H node265 := by
  calc
    injectiveMoment H raw7467 = injectiveMoment H raw7467step0 := by
      have heq : raw7467step0 = raw7467.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7467).symm
    injectiveMoment H raw7467step0 = injectiveMoment H raw7467step1 := by
      have heq : raw7467step1 = (fun i j => raw7467step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7467step0 permutation10 permutation3
    _ = injectiveMoment H node265 := by rfl

def raw7468 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, 2, -2, 2], ![3, -2, 1, -2]]

def raw7468step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, -2, 1], ![0, 2, -2]]

def raw7468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

theorem canonical7468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7468 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw7468 = injectiveMoment H raw7468step0 := by
      have heq : raw7468step0 = raw7468.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7468).symm
    injectiveMoment H raw7468step0 = injectiveMoment H raw7468step1 := by
      have heq : raw7468step1 = (fun i j => raw7468step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7468step0 permutation10 permutation3
    _ = injectiveMoment H node274 := by rfl

def raw7469 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, 2, 1, -1], ![3, -2, -2, 1]]

def raw7469step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![0, -1, 1]]

def raw7469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical7469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7469 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw7469 = injectiveMoment H raw7469step0 := by
      have heq : raw7469step0 = raw7469.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7469).symm
    injectiveMoment H raw7469step0 = injectiveMoment H raw7469step1 := by
      have heq : raw7469step1 = (fun i j => raw7469step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7469step0 permutation13 permutation3
    _ = injectiveMoment H node268 := by rfl

def raw7470 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, 3, -2, 1], ![3, -3, 1, -1]]

def raw7470step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -2, 1], ![0, 1, -1]]

def raw7470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

theorem canonical7470 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7470 = injectiveMoment H node273 := by
  calc
    injectiveMoment H raw7470 = injectiveMoment H raw7470step0 := by
      have heq : raw7470step0 = raw7470.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7470).symm
    injectiveMoment H raw7470step0 = injectiveMoment H raw7470step1 := by
      have heq : raw7470step1 = (fun i j => raw7470step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7470step0 permutation13 permutation3
    _ = injectiveMoment H node273 := by rfl

def raw7471 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -3, 1, 3], ![2, 3, -2, -3]]

def raw7471step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![1, 1, -2], ![0, 3, -3]]

def raw7471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

theorem canonical7471 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7471 = injectiveMoment H node277 := by
  calc
    injectiveMoment H raw7471 = injectiveMoment H raw7471step0 := by
      have heq : raw7471step0 = raw7471.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7471).symm
    injectiveMoment H raw7471step0 = injectiveMoment H raw7471step1 := by
      have heq : raw7471step1 = (fun i j => raw7471step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7471step0 permutation10 permutation3
    _ = injectiveMoment H node277 := by rfl

def raw7472 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -2, -2, 5], ![2, 2, 1, -5]]

def raw7472step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![1, -2, 1], ![0, 5, -5]]

def raw7472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

theorem canonical7472 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7472 = injectiveMoment H node282 := by
  calc
    injectiveMoment H raw7472 = injectiveMoment H raw7472step0 := by
      have heq : raw7472step0 = raw7472.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7472).symm
    injectiveMoment H raw7472step0 = injectiveMoment H raw7472step1 := by
      have heq : raw7472step1 = (fun i j => raw7472step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7472step0 permutation10 permutation3
    _ = injectiveMoment H node282 := by rfl

def raw7473 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -2, 1, 2], ![2, 2, -2, -2]]

def raw7473step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![0, 2, -2]]

def raw7473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical7473 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7473 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw7473 = injectiveMoment H raw7473step0 := by
      have heq : raw7473step0 = raw7473.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7473).symm
    injectiveMoment H raw7473step0 = injectiveMoment H raw7473step1 := by
      have heq : raw7473step1 = (fun i j => raw7473step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7473step0 permutation10 permutation3
    _ = injectiveMoment H node279 := by rfl

def raw7474 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw7474step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw7474step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical7474 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7474 = injectiveMoment H node3355 := by
  calc
    injectiveMoment H raw7474 = injectiveMoment H raw7474step0 := by
      have heq : raw7474step0 = -raw7474 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7474).symm
    injectiveMoment H raw7474step0 = injectiveMoment H raw7474step1 := by
      have heq : raw7474step1 = (fun i j => raw7474step0 (permutation384 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7474step0 permutation384 permutation15
    _ = injectiveMoment H node3355 := by rfl

def raw7475 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw7475step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw7475step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical7475 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7475 = injectiveMoment H node2972 := by
  calc
    injectiveMoment H raw7475 = injectiveMoment H raw7475step0 := by
      have heq : raw7475step0 = -raw7475 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7475).symm
    injectiveMoment H raw7475step0 = injectiveMoment H raw7475step1 := by
      have heq : raw7475step1 = (fun i j => raw7475step0 (permutation328 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7475step0 permutation328 permutation17
    _ = injectiveMoment H node2972 := by rfl

def raw7476 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 2, -4, 3], ![2, -2, 3, -3]]

def raw7476step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -4, 3], ![0, 3, -3]]

def raw7476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-1, 4, -3], ![0, -3, 3]]

def raw7476step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical7476 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7476 = injectiveMoment H node257 := by
  calc
    injectiveMoment H raw7476 = injectiveMoment H raw7476step0 := by
      have heq : raw7476step0 = raw7476.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7476).symm
    injectiveMoment H raw7476step0 = injectiveMoment H raw7476step1 := by
      have heq : raw7476step1 = -raw7476step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7476step0).symm
    injectiveMoment H raw7476step1 = injectiveMoment H raw7476step2 := by
      have heq : raw7476step2 = (fun i j => raw7476step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7476step1 permutation24 permutation4
    _ = injectiveMoment H node257 := by rfl

def raw7477 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 2, -3, 2], ![2, -2, 2, -2]]

def raw7477step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -3, 2], ![0, 2, -2]]

def raw7477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-1, 3, -2], ![0, -2, 2]]

def raw7477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

theorem canonical7477 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7477 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw7477 = injectiveMoment H raw7477step0 := by
      have heq : raw7477step0 = raw7477.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7477).symm
    injectiveMoment H raw7477step0 = injectiveMoment H raw7477step1 := by
      have heq : raw7477step1 = -raw7477step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7477step0).symm
    injectiveMoment H raw7477step1 = injectiveMoment H raw7477step2 := by
      have heq : raw7477step2 = (fun i j => raw7477step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7477step1 permutation24 permutation4
    _ = injectiveMoment H node274 := by rfl

def raw7478 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 2, -2, 1], ![2, -2, 1, -1]]

def raw7478step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![0, 1, -1]]

def raw7478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical7478 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7478 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw7478 = injectiveMoment H raw7478step0 := by
      have heq : raw7478step0 = raw7478.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7478).symm
    injectiveMoment H raw7478step0 = injectiveMoment H raw7478step1 := by
      have heq : raw7478step1 = (fun i j => raw7478step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7478step0 permutation13 permutation3
    _ = injectiveMoment H node288 := by rfl

def raw7479 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 3, -4, 2], ![2, -3, 3, -2]]

def raw7479step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -4, 3], ![0, 2, -2]]

def raw7479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-1, 4, -3], ![0, -2, 2]]

def raw7479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical7479 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7479 = injectiveMoment H node257 := by
  calc
    injectiveMoment H raw7479 = injectiveMoment H raw7479step0 := by
      have heq : raw7479step0 = raw7479.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7479).symm
    injectiveMoment H raw7479step0 = injectiveMoment H raw7479step1 := by
      have heq : raw7479step1 = -raw7479step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7479step0).symm
    injectiveMoment H raw7479step1 = injectiveMoment H raw7479step2 := by
      have heq : raw7479step2 = (fun i j => raw7479step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7479step1 permutation26 permutation4
    _ = injectiveMoment H node257 := by rfl

def raw7480 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 4, -2, -1], ![2, -4, 1, 1]]

def raw7480step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![0, -1, 1]]

def raw7480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

theorem canonical7480 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7480 = injectiveMoment H node286 := by
  calc
    injectiveMoment H raw7480 = injectiveMoment H raw7480step0 := by
      have heq : raw7480step0 = raw7480.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7480).symm
    injectiveMoment H raw7480step0 = injectiveMoment H raw7480step1 := by
      have heq : raw7480step1 = (fun i j => raw7480step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7480step0 permutation13 permutation3
    _ = injectiveMoment H node286 := by rfl

def raw7481 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -3, 1, 2], ![1, 3, -2, -2]]

def raw7481step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![1, 1, -2], ![0, 2, -2]]

def raw7481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-1, -1, 2], ![0, -2, 2]]

def raw7481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7481 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7481 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw7481 = injectiveMoment H raw7481step0 := by
      have heq : raw7481step0 = raw7481.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7481).symm
    injectiveMoment H raw7481step0 = injectiveMoment H raw7481step1 := by
      have heq : raw7481step1 = -raw7481step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7481step0).symm
    injectiveMoment H raw7481step1 = injectiveMoment H raw7481step2 := by
      have heq : raw7481step2 = (fun i j => raw7481step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7481step1 permutation26 permutation3
    _ = injectiveMoment H node280 := by rfl

def raw7482 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![1, 2, 1, -4]]

def raw7482step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![1, -2, 1], ![0, 4, -4]]

def raw7482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, 2, -1], ![0, -4, 4]]

def raw7482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7482 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7482 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw7482 = injectiveMoment H raw7482step0 := by
      have heq : raw7482step0 = raw7482.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7482).symm
    injectiveMoment H raw7482step0 = injectiveMoment H raw7482step1 := by
      have heq : raw7482step1 = -raw7482step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7482step0).symm
    injectiveMoment H raw7482step1 = injectiveMoment H raw7482step2 := by
      have heq : raw7482step2 = (fun i j => raw7482step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7482step1 permutation24 permutation4
    _ = injectiveMoment H node281 := by rfl

def raw7483 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 1, 1], ![1, 2, -2, -1]]

def raw7483step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1]]

def raw7483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, -1, 2], ![0, -1, 1]]

def raw7483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7483 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7483 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7483 = injectiveMoment H raw7483step0 := by
      have heq : raw7483step0 = raw7483.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7483).symm
    injectiveMoment H raw7483step0 = injectiveMoment H raw7483step1 := by
      have heq : raw7483step1 = -raw7483step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7483step0).symm
    injectiveMoment H raw7483step1 = injectiveMoment H raw7483step2 := by
      have heq : raw7483step2 = (fun i j => raw7483step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7483step1 permutation26 permutation3
    _ = injectiveMoment H node284 := by rfl

def raw7484 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7484step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 3, -4], ![0, 0, -2, 2], ![-1, -1, 0, 2]]

def raw7484step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical7484 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7484 = injectiveMoment H node1031 := by
  calc
    injectiveMoment H raw7484 = injectiveMoment H raw7484step0 := by
      have heq : raw7484step0 = -raw7484 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7484).symm
    injectiveMoment H raw7484step0 = injectiveMoment H raw7484step1 := by
      have heq : raw7484step1 = (fun i j => raw7484step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7484step0 permutation31 permutation15
    _ = injectiveMoment H node1031 := by rfl

def raw7485 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical7485 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7485 = injectiveMoment H node1168 := by
  calc
    injectiveMoment H raw7485 = injectiveMoment H raw7485step0 := by
      have heq : raw7485step0 = (fun i j => raw7485 (permutation16 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7485 permutation16 permutation15
    _ = injectiveMoment H node1168 := by rfl

def raw7486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw7486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical7486 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7486 = injectiveMoment H node1167 := by
  calc
    injectiveMoment H raw7486 = injectiveMoment H raw7486step0 := by
      have heq : raw7486step0 = (fun i j => raw7486 (permutation16 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7486 permutation16 permutation15
    _ = injectiveMoment H node1167 := by rfl

def raw7487 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical7487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7487 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw7487 = injectiveMoment H raw7487step0 := by
      have heq : raw7487step0 = (fun i j => raw7487 (permutation16 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7487 permutation16 permutation15
    _ = injectiveMoment H node1202 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
