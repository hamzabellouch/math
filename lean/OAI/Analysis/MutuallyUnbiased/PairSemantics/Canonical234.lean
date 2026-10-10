import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7488 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw7488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 1, -2], ![0, 0, 2, -2], ![-1, -1, -2, 4]]

def raw7488step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical7488 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7488 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw7488 = injectiveMoment H raw7488step0 := by
      have heq : raw7488step0 = -raw7488 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7488).symm
    injectiveMoment H raw7488step0 = injectiveMoment H raw7488step1 := by
      have heq : raw7488step1 = (fun i j => raw7488step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7488step0 permutation31 permutation15
    _ = injectiveMoment H node914 := by rfl

def raw7489 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw7489step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw7489step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical7489 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7489 = injectiveMoment H node3355 := by
  calc
    injectiveMoment H raw7489 = injectiveMoment H raw7489step0 := by
      have heq : raw7489step0 = -raw7489 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7489).symm
    injectiveMoment H raw7489step0 = injectiveMoment H raw7489step1 := by
      have heq : raw7489step1 = (fun i j => raw7489step0 (permutation402 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7489step0 permutation402 permutation11
    _ = injectiveMoment H node3355 := by rfl

def raw7490 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw7490step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw7490step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical7490 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7490 = injectiveMoment H node2973 := by
  calc
    injectiveMoment H raw7490 = injectiveMoment H raw7490step0 := by
      have heq : raw7490step0 = -raw7490 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7490).symm
    injectiveMoment H raw7490step0 = injectiveMoment H raw7490step1 := by
      have heq : raw7490step1 = (fun i j => raw7490step0 (permutation328 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7490step0 permutation328 permutation17
    _ = injectiveMoment H node2973 := by rfl

def raw7491 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw7491step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw7491step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical7491 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7491 = injectiveMoment H node3356 := by
  calc
    injectiveMoment H raw7491 = injectiveMoment H raw7491step0 := by
      have heq : raw7491step0 = -raw7491 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7491).symm
    injectiveMoment H raw7491step0 = injectiveMoment H raw7491step1 := by
      have heq : raw7491step1 = (fun i j => raw7491step0 (permutation400 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7491step0 permutation400 permutation11
    _ = injectiveMoment H node3356 := by rfl

def raw7492 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw7492step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw7492step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical7492 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7492 = injectiveMoment H node3455 := by
  calc
    injectiveMoment H raw7492 = injectiveMoment H raw7492step0 := by
      have heq : raw7492step0 = -raw7492 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7492).symm
    injectiveMoment H raw7492step0 = injectiveMoment H raw7492step1 := by
      have heq : raw7492step1 = (fun i j => raw7492step0 (permutation301 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7492step0 permutation301 permutation9
    _ = injectiveMoment H node3455 := by rfl

def raw7493 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 1, 1, -3]]

def raw7493step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, -1, -1, 3]]

def raw7493step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical7493 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7493 = injectiveMoment H node3374 := by
  calc
    injectiveMoment H raw7493 = injectiveMoment H raw7493step0 := by
      have heq : raw7493step0 = -raw7493 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7493).symm
    injectiveMoment H raw7493step0 = injectiveMoment H raw7493step1 := by
      have heq : raw7493step1 = (fun i j => raw7493step0 (permutation386 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7493step0 permutation386 permutation9
    _ = injectiveMoment H node3374 := by rfl

def raw7494 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 1, 1, -2]]

def raw7494step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical7494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7494 = injectiveMoment H node3434 := by
  calc
    injectiveMoment H raw7494 = injectiveMoment H raw7494step0 := by
      have heq : raw7494step0 = (fun i j => raw7494 (permutation200 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7494 permutation200 permutation13
    _ = injectiveMoment H node3434 := by rfl

def raw7495 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 0, -1, 1], ![0, 2, 1, -3]]

def raw7495step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, -2, -1, 3]]

def raw7495step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical7495 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7495 = injectiveMoment H node3457 := by
  calc
    injectiveMoment H raw7495 = injectiveMoment H raw7495step0 := by
      have heq : raw7495step0 = -raw7495 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7495).symm
    injectiveMoment H raw7495step0 = injectiveMoment H raw7495step1 := by
      have heq : raw7495step1 = (fun i j => raw7495step0 (permutation256 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7495step0 permutation256 permutation11
    _ = injectiveMoment H node3457 := by rfl

def raw7496 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 2, 1, -2]]

def raw7496step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical7496 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7496 = injectiveMoment H node3044 := by
  calc
    injectiveMoment H raw7496 = injectiveMoment H raw7496step0 := by
      have heq : raw7496step0 = (fun i j => raw7496 (permutation330 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7496 permutation330 permutation28
    _ = injectiveMoment H node3044 := by rfl

def raw7497 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![1, 0, 2, -3]]

def raw7497step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 0, 3, -3], ![-1, 0, -2, 3]]

def raw7497step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-1, -2, 3]]

def raw7497step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7497 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7497 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7497 = injectiveMoment H raw7497step0 := by
      have heq : raw7497step0 = -raw7497 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7497).symm
    injectiveMoment H raw7497step0 = injectiveMoment H raw7497step1 := by
      have hz : ∀ i, raw7497step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7497step1 = (fun i j => raw7497step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7497step0 permutation15 hz
    injectiveMoment H raw7497step1 = injectiveMoment H raw7497step2 := by
      have heq : raw7497step2 = (fun i j => raw7497step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7497step1 permutation8 permutation3
    _ = injectiveMoment H node58 := by rfl

def raw7498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![0, 2, -1, -1]]

def raw7498step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical7498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7498 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw7498 = injectiveMoment H raw7498step0 := by
      have heq : raw7498step0 = raw7498.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7498).symm
    injectiveMoment H raw7498step0 = injectiveMoment H raw7498step1 := by
      have heq : raw7498step1 = (fun i j => raw7498step0 (permutation28 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7498step0 permutation28 permutation22
    _ = injectiveMoment H node1242 := by rfl

def raw7499 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![1, 0, 1, -2]]

def raw7499step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 0, 2, -2], ![-1, 0, -1, 2]]

def raw7499step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-1, -1, 2]]

def raw7499step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7499 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7499 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw7499 = injectiveMoment H raw7499step0 := by
      have heq : raw7499step0 = -raw7499 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7499).symm
    injectiveMoment H raw7499step0 = injectiveMoment H raw7499step1 := by
      have hz : ∀ i, raw7499step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7499step1 = (fun i j => raw7499step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7499step0 permutation15 hz
    injectiveMoment H raw7499step1 = injectiveMoment H raw7499step2 := by
      have heq : raw7499step2 = (fun i j => raw7499step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7499step1 permutation8 permutation3
    _ = injectiveMoment H node62 := by rfl

def raw7500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7500step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical7500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7500 = injectiveMoment H node2750 := by
  calc
    injectiveMoment H raw7500 = injectiveMoment H raw7500step0 := by
      have heq : raw7500step0 = (fun i j => raw7500 (permutation35 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7500 permutation35 permutation13
    _ = injectiveMoment H node2750 := by rfl

def raw7501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw7501step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 1, -1]]

def raw7501step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical7501 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7501 = injectiveMoment H node1118 := by
  calc
    injectiveMoment H raw7501 = injectiveMoment H raw7501step0 := by
      have heq : raw7501step0 = -raw7501 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7501).symm
    injectiveMoment H raw7501step0 = injectiveMoment H raw7501step1 := by
      have heq : raw7501step1 = (fun i j => raw7501step0 (permutation32 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7501step0 permutation32 permutation13
    _ = injectiveMoment H node1118 := by rfl

def raw7502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical7502 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7502 = injectiveMoment H node2823 := by
  rfl

def raw7503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![1, 1, 0, -2], ![0, -1, -1, 2]]

def raw7503step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical7503 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7503 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw7503 = injectiveMoment H raw7503step0 := by
      have heq : raw7503step0 = raw7503.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7503).symm
    injectiveMoment H raw7503step0 = injectiveMoment H raw7503step1 := by
      have heq : raw7503step1 = (fun i j => raw7503step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7503step0 permutation27 permutation17
    _ = injectiveMoment H node1044 := by rfl

def raw7504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw7504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![1, 1, 0, -2], ![0, -1, -2, 3]]

def raw7504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![-1, -1, 0, 2], ![0, 1, 2, -3]]

def raw7504step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical7504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7504 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw7504 = injectiveMoment H raw7504step0 := by
      have heq : raw7504step0 = raw7504.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7504).symm
    injectiveMoment H raw7504step0 = injectiveMoment H raw7504step1 := by
      have heq : raw7504step1 = -raw7504step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7504step0).symm
    injectiveMoment H raw7504step1 = injectiveMoment H raw7504step2 := by
      have heq : raw7504step2 = (fun i j => raw7504step1 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7504step1 permutation23 permutation15
    _ = injectiveMoment H node1032 := by rfl

def raw7505 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def raw7505step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![0, 2, -2]]

def raw7505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, 3, -2], ![0, -2, 2]]

def raw7505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7505 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7505 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7505 = injectiveMoment H raw7505step0 := by
      have heq : raw7505step0 = raw7505.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7505).symm
    injectiveMoment H raw7505step0 = injectiveMoment H raw7505step1 := by
      have heq : raw7505step1 = -raw7505step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7505step0).symm
    injectiveMoment H raw7505step1 = injectiveMoment H raw7505step2 := by
      have heq : raw7505step2 = (fun i j => raw7505step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7505step1 permutation24 permutation4
    _ = injectiveMoment H node272 := by rfl

def raw7506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw7506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![0, -1, -1, 2]]

def raw7506step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical7506 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7506 = injectiveMoment H node1039 := by
  calc
    injectiveMoment H raw7506 = injectiveMoment H raw7506step0 := by
      have heq : raw7506step0 = raw7506.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7506).symm
    injectiveMoment H raw7506step0 = injectiveMoment H raw7506step1 := by
      have heq : raw7506step1 = (fun i j => raw7506step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7506step0 permutation28 permutation17
    _ = injectiveMoment H node1039 := by rfl

def raw7507 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw7507step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, -2, 2]]

def raw7507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![0, 2, -2]]

def raw7507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7507 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7507 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7507 = injectiveMoment H raw7507step0 := by
      have heq : raw7507step0 = raw7507.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7507).symm
    injectiveMoment H raw7507step0 = injectiveMoment H raw7507step1 := by
      have heq : raw7507step1 = -raw7507step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7507step0).symm
    injectiveMoment H raw7507step1 = injectiveMoment H raw7507step2 := by
      have heq : raw7507step2 = (fun i j => raw7507step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7507step1 permutation24 permutation3
    _ = injectiveMoment H node284 := by rfl

def raw7508 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw7508step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![0, -3, 3]]

def raw7508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![0, 3, -3]]

def raw7508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7508 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7508 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw7508 = injectiveMoment H raw7508step0 := by
      have heq : raw7508step0 = raw7508.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7508).symm
    injectiveMoment H raw7508step0 = injectiveMoment H raw7508step1 := by
      have heq : raw7508step1 = -raw7508step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7508step0).symm
    injectiveMoment H raw7508step1 = injectiveMoment H raw7508step2 := by
      have heq : raw7508step2 = (fun i j => raw7508step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7508step1 permutation24 permutation3
    _ = injectiveMoment H node269 := by rfl

def raw7509 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, -4, 2], ![1, -2, 3, -2]]

def raw7509step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -4, 3], ![0, 2, -2]]

def raw7509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 4, -3], ![0, -2, 2]]

def raw7509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7509 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7509 = injectiveMoment H node256 := by
  calc
    injectiveMoment H raw7509 = injectiveMoment H raw7509step0 := by
      have heq : raw7509step0 = raw7509.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7509).symm
    injectiveMoment H raw7509step0 = injectiveMoment H raw7509step1 := by
      have heq : raw7509step1 = -raw7509step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7509step0).symm
    injectiveMoment H raw7509step1 = injectiveMoment H raw7509step2 := by
      have heq : raw7509step2 = (fun i j => raw7509step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7509step1 permutation24 permutation4
    _ = injectiveMoment H node256 := by rfl

def raw7510 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, -3, 1], ![1, -2, 2, -1]]

def raw7510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![0, 1, -1]]

def raw7510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 3, -2], ![0, -1, 1]]

def raw7510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7510 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7510 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7510 = injectiveMoment H raw7510step0 := by
      have heq : raw7510step0 = raw7510.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7510).symm
    injectiveMoment H raw7510step0 = injectiveMoment H raw7510step1 := by
      have heq : raw7510step1 = -raw7510step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7510step0).symm
    injectiveMoment H raw7510step1 = injectiveMoment H raw7510step2 := by
      have heq : raw7510step2 = (fun i j => raw7510step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7510step1 permutation26 permutation4
    _ = injectiveMoment H node272 := by rfl

def raw7511 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw7511step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![0, -2, 2]]

def raw7511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7511 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7511 = injectiveMoment H raw7511step0 := by
      have heq : raw7511step0 = raw7511.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7511).symm
    injectiveMoment H raw7511step0 = injectiveMoment H raw7511step1 := by
      have heq : raw7511step1 = (fun i j => raw7511step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7511step0 permutation13 permutation3
    _ = injectiveMoment H node291 := by rfl

def raw7512 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw7512step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![0, -3, 3]]

def raw7512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![0, 3, -3]]

def raw7512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7512 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7512 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw7512 = injectiveMoment H raw7512step0 := by
      have heq : raw7512step0 = raw7512.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7512).symm
    injectiveMoment H raw7512step0 = injectiveMoment H raw7512step1 := by
      have heq : raw7512step1 = -raw7512step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7512step0).symm
    injectiveMoment H raw7512step1 = injectiveMoment H raw7512step2 := by
      have heq : raw7512step2 = (fun i j => raw7512step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7512step1 permutation24 permutation3
    _ = injectiveMoment H node280 := by rfl

def raw7513 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 3, -4, 1], ![1, -3, 3, -1]]

def raw7513step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![1, -4, 3], ![0, 1, -1]]

def raw7513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 4, -3], ![0, -1, 1]]

def raw7513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7513 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7513 = injectiveMoment H node255 := by
  calc
    injectiveMoment H raw7513 = injectiveMoment H raw7513step0 := by
      have heq : raw7513step0 = raw7513.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7513).symm
    injectiveMoment H raw7513step0 = injectiveMoment H raw7513step1 := by
      have heq : raw7513step1 = -raw7513step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7513step0).symm
    injectiveMoment H raw7513step1 = injectiveMoment H raw7513step2 := by
      have heq : raw7513step2 = (fun i j => raw7513step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7513step1 permutation26 permutation4
    _ = injectiveMoment H node255 := by rfl

def raw7514 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 4, -2, -2], ![1, -4, 1, 2]]

def raw7514step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 4, -4], ![1, -2, 1], ![0, -2, 2]]

def raw7514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -4, 4], ![-1, 2, -1], ![0, 2, -2]]

def raw7514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7514 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7514 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw7514 = injectiveMoment H raw7514step0 := by
      have heq : raw7514step0 = raw7514.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7514).symm
    injectiveMoment H raw7514step0 = injectiveMoment H raw7514step1 := by
      have heq : raw7514step1 = -raw7514step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7514step0).symm
    injectiveMoment H raw7514step1 = injectiveMoment H raw7514step2 := by
      have heq : raw7514step2 = (fun i j => raw7514step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7514step1 permutation26 permutation4
    _ = injectiveMoment H node281 := by rfl

def raw7515 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![1, -3, 1, 1], ![0, 3, -2, -1]]

def raw7515step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![1, 1, -2], ![0, 1, -1]]

def raw7515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-1, -1, 2], ![0, -1, 1]]

def raw7515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7515 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7515 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw7515 = injectiveMoment H raw7515step0 := by
      have heq : raw7515step0 = raw7515.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7515).symm
    injectiveMoment H raw7515step0 = injectiveMoment H raw7515step1 := by
      have heq : raw7515step1 = -raw7515step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7515step0).symm
    injectiveMoment H raw7515step1 = injectiveMoment H raw7515step2 := by
      have heq : raw7515step2 = (fun i j => raw7515step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7515step1 permutation26 permutation3
    _ = injectiveMoment H node285 := by rfl

def raw7516 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![1, -2, -2, 3], ![0, 2, 1, -3]]

def raw7516step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![1, -2, 1], ![0, 3, -3]]

def raw7516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-1, 2, -1], ![0, -3, 3]]

def raw7516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7516 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7516 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw7516 = injectiveMoment H raw7516step0 := by
      have heq : raw7516step0 = raw7516.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7516).symm
    injectiveMoment H raw7516step0 = injectiveMoment H raw7516step1 := by
      have heq : raw7516step1 = -raw7516step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7516step0).symm
    injectiveMoment H raw7516step1 = injectiveMoment H raw7516step2 := by
      have heq : raw7516step2 = (fun i j => raw7516step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7516step1 permutation24 permutation4
    _ = injectiveMoment H node280 := by rfl

def raw7517 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 2, -2, 3], ![4, -2, 0, -2]]

def raw7517step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![2, -2, 0], ![-1, 3, -2]]

def raw7517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 2, 0], ![1, -3, 2]]

def raw7517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

theorem canonical7517 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7517 = injectiveMoment H node211 := by
  calc
    injectiveMoment H raw7517 = injectiveMoment H raw7517step0 := by
      have heq : raw7517step0 = raw7517.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7517).symm
    injectiveMoment H raw7517step0 = injectiveMoment H raw7517step1 := by
      have heq : raw7517step1 = -raw7517step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7517step0).symm
    injectiveMoment H raw7517step1 = injectiveMoment H raw7517step2 := by
      have heq : raw7517step2 = (fun i j => raw7517step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7517step1 permutation23 permutation4
    _ = injectiveMoment H node211 := by rfl

def raw7518 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 2, -1, 2], ![4, -2, -1, -1]]

def raw7518step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![2, -1, -1], ![-1, 2, -1]]

def raw7518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 1, 1], ![1, -2, 1]]

def raw7518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical7518 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7518 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw7518 = injectiveMoment H raw7518step0 := by
      have heq : raw7518step0 = raw7518.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7518).symm
    injectiveMoment H raw7518step0 = injectiveMoment H raw7518step1 := by
      have heq : raw7518step1 = -raw7518step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7518step0).symm
    injectiveMoment H raw7518step1 = injectiveMoment H raw7518step2 := by
      have heq : raw7518step2 = (fun i j => raw7518step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7518step1 permutation24 permutation3
    _ = injectiveMoment H node225 := by rfl

def raw7519 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 2, 0, 1], ![4, -2, -2, 0]]

def raw7519step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![2, 0, -2], ![-1, 1, 0]]

def raw7519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 0, 2], ![1, -1, 0]]

def raw7519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7519 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7519 = injectiveMoment H raw7519step0 := by
      have heq : raw7519step0 = raw7519.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7519).symm
    injectiveMoment H raw7519step0 = injectiveMoment H raw7519step1 := by
      have heq : raw7519step1 = -raw7519step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7519step0).symm
    injectiveMoment H raw7519step1 = injectiveMoment H raw7519step2 := by
      have heq : raw7519step2 = (fun i j => raw7519step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7519step1 permutation24 permutation3
    _ = injectiveMoment H node201 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
