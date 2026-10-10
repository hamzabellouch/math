import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7328step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 3, -3], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw7328step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical7328 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7328 = injectiveMoment H node1181 := by
  calc
    injectiveMoment H raw7328 = injectiveMoment H raw7328step0 := by
      have heq : raw7328step0 = -raw7328 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7328).symm
    injectiveMoment H raw7328step0 = injectiveMoment H raw7328step1 := by
      have heq : raw7328step1 = (fun i j => raw7328step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7328step0 permutation23 permutation15
    _ = injectiveMoment H node1181 := by rfl

def raw7329 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -3, 3], ![1, 0, 3, -4]]

def raw7329step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 3, -3], ![-1, 0, -3, 4]]

def raw7329step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-1, -3, 4]]

def raw7329step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7329 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7329 = injectiveMoment H raw7329step0 := by
      have heq : raw7329step0 = -raw7329 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7329).symm
    injectiveMoment H raw7329step0 = injectiveMoment H raw7329step1 := by
      have hz : ∀ i, raw7329step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7329step1 = (fun i j => raw7329step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7329step0 permutation15 hz
    injectiveMoment H raw7329step1 = injectiveMoment H raw7329step2 := by
      have heq : raw7329step2 = (fun i j => raw7329step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7329step1 permutation8 permutation3
    _ = injectiveMoment H node53 := by rfl

def raw7330 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7330step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 2, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0]]

def raw7330step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical7330 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7330 = injectiveMoment H node1221 := by
  calc
    injectiveMoment H raw7330 = injectiveMoment H raw7330step0 := by
      have heq : raw7330step0 = -raw7330 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7330).symm
    injectiveMoment H raw7330step0 = injectiveMoment H raw7330step1 := by
      have heq : raw7330step1 = (fun i j => raw7330step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7330step0 permutation23 permutation15
    _ = injectiveMoment H node1221 := by rfl

def raw7331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7331step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 1, 1, -1]]

def raw7331step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem canonical7331 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7331 = injectiveMoment H node1177 := by
  calc
    injectiveMoment H raw7331 = injectiveMoment H raw7331step0 := by
      have heq : raw7331step0 = -raw7331 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7331).symm
    injectiveMoment H raw7331step0 = injectiveMoment H raw7331step1 := by
      have heq : raw7331step1 = (fun i j => raw7331step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7331step0 permutation23 permutation15
    _ = injectiveMoment H node1177 := by rfl

def raw7332 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw7332step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, -2, -1, 3], ![1, 2, -1, -2]]

def raw7332step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![-1, -2, 1, 2]]

def raw7332step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical7332 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7332 = injectiveMoment H node832 := by
  calc
    injectiveMoment H raw7332 = injectiveMoment H raw7332step0 := by
      have heq : raw7332step0 = raw7332.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7332).symm
    injectiveMoment H raw7332step0 = injectiveMoment H raw7332step1 := by
      have heq : raw7332step1 = -raw7332step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7332step0).symm
    injectiveMoment H raw7332step1 = injectiveMoment H raw7332step2 := by
      have heq : raw7332step2 = (fun i j => raw7332step1 (permutation30 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7332step1 permutation30 permutation9
    _ = injectiveMoment H node832 := by rfl

def raw7333 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![1, 0, 2, -3]]

def raw7333step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 2, -2], ![-1, 0, -2, 3]]

def raw7333step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, -2, 3]]

def raw7333step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7333 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7333 = injectiveMoment H raw7333step0 := by
      have heq : raw7333step0 = -raw7333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7333).symm
    injectiveMoment H raw7333step0 = injectiveMoment H raw7333step1 := by
      have hz : ∀ i, raw7333step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7333step1 = (fun i j => raw7333step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7333step0 permutation15 hz
    injectiveMoment H raw7333step1 = injectiveMoment H raw7333step2 := by
      have heq : raw7333step2 = (fun i j => raw7333step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7333step1 permutation8 permutation3
    _ = injectiveMoment H node57 := by rfl

def raw7334 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7334step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -2, -2, 4]]

def raw7334step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical7334 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7334 = injectiveMoment H node2878 := by
  calc
    injectiveMoment H raw7334 = injectiveMoment H raw7334step0 := by
      have heq : raw7334step0 = -raw7334 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7334).symm
    injectiveMoment H raw7334step0 = injectiveMoment H raw7334step1 := by
      have heq : raw7334step1 = (fun i j => raw7334step0 (permutation324 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7334step0 permutation324 permutation23
    _ = injectiveMoment H node2878 := by rfl

def raw7335 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7335step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -1, -2, 3]]

def raw7335step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical7335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7335 = injectiveMoment H node3012 := by
  calc
    injectiveMoment H raw7335 = injectiveMoment H raw7335step0 := by
      have heq : raw7335step0 = -raw7335 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7335).symm
    injectiveMoment H raw7335step0 = injectiveMoment H raw7335step1 := by
      have heq : raw7335step1 = (fun i j => raw7335step0 (permutation325 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7335step0 permutation325 permutation23
    _ = injectiveMoment H node3012 := by rfl

def raw7336 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7336step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical7336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7336 = injectiveMoment H node3439 := by
  calc
    injectiveMoment H raw7336 = injectiveMoment H raw7336step0 := by
      have heq : raw7336step0 = (fun i j => raw7336 (permutation152 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7336 permutation152 permutation11
    _ = injectiveMoment H node3439 := by rfl

def raw7337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7337step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical7337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7337 = injectiveMoment H node2749 := by
  calc
    injectiveMoment H raw7337 = injectiveMoment H raw7337step0 := by
      have heq : raw7337step0 = (fun i j => raw7337 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7337 permutation33 permutation11
    _ = injectiveMoment H node2749 := by rfl

def raw7338 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, -1, 0, 1], ![0, 2, 2, -4]]

def raw7338step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical7338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7338 = injectiveMoment H node3439 := by
  calc
    injectiveMoment H raw7338 = injectiveMoment H raw7338step0 := by
      have heq : raw7338step0 = (fun i j => raw7338 (permutation154 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7338 permutation154 permutation11
    _ = injectiveMoment H node3439 := by rfl

def raw7339 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 2, 2, -3]]

def raw7339step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, -2, -2, 3]]

def raw7339step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical7339 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7339 = injectiveMoment H node2888 := by
  calc
    injectiveMoment H raw7339 = injectiveMoment H raw7339step0 := by
      have heq : raw7339step0 = -raw7339 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7339).symm
    injectiveMoment H raw7339step0 = injectiveMoment H raw7339step1 := by
      have heq : raw7339step1 = (fun i j => raw7339step0 (permutation324 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7339step0 permutation324 permutation23
    _ = injectiveMoment H node2888 := by rfl

def raw7340 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7340step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical7340 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7340 = injectiveMoment H node3441 := by
  calc
    injectiveMoment H raw7340 = injectiveMoment H raw7340step0 := by
      have heq : raw7340step0 = (fun i j => raw7340 (permutation152 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7340 permutation152 permutation11
    _ = injectiveMoment H node3441 := by rfl

def raw7341 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, -1, 0, 1], ![0, 1, 2, -3]]

def raw7341step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical7341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7341 = injectiveMoment H node3441 := by
  calc
    injectiveMoment H raw7341 = injectiveMoment H raw7341step0 := by
      have heq : raw7341step0 = (fun i j => raw7341 (permutation154 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7341 permutation154 permutation11
    _ = injectiveMoment H node3441 := by rfl

def raw7342 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 2, -2]]

def raw7342step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical7342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7342 = injectiveMoment H node3081 := by
  calc
    injectiveMoment H raw7342 = injectiveMoment H raw7342step0 := by
      have heq : raw7342step0 = (fun i j => raw7342 (permutation366 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7342 permutation366 permutation27
    _ = injectiveMoment H node3081 := by rfl

def raw7343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7343step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, -1, 1, 0], ![1, 1, -3, 1]]

def raw7343step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![-1, -1, 3, -1]]

def raw7343step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7343 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7343 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw7343 = injectiveMoment H raw7343step0 := by
      have heq : raw7343step0 = raw7343.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7343).symm
    injectiveMoment H raw7343step0 = injectiveMoment H raw7343step1 := by
      have heq : raw7343step1 = -raw7343step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7343step0).symm
    injectiveMoment H raw7343step1 = injectiveMoment H raw7343step2 := by
      have heq : raw7343step2 = (fun i j => raw7343step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7343step1 permutation29 permutation16
    _ = injectiveMoment H node974 := by rfl

def raw7344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw7344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, -1, 2, -1], ![1, 1, -4, 2]]

def raw7344step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, 1, -2, 1], ![-1, -1, 4, -2]]

def raw7344step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical7344 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7344 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw7344 = injectiveMoment H raw7344step0 := by
      have heq : raw7344step0 = raw7344.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7344).symm
    injectiveMoment H raw7344step0 = injectiveMoment H raw7344step1 := by
      have heq : raw7344step1 = -raw7344step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7344step0).symm
    injectiveMoment H raw7344step1 = injectiveMoment H raw7344step2 := by
      have heq : raw7344step2 = (fun i j => raw7344step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7344step1 permutation29 permutation16
    _ = injectiveMoment H node914 := by rfl

def raw7345 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7345step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical7345 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7345 = injectiveMoment H node3399 := by
  calc
    injectiveMoment H raw7345 = injectiveMoment H raw7345step0 := by
      have heq : raw7345step0 = (fun i j => raw7345 (permutation225 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7345 permutation225 permutation11
    _ = injectiveMoment H node3399 := by rfl

def raw7346 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7346step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical7346 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7346 = injectiveMoment H node3399 := by
  calc
    injectiveMoment H raw7346 = injectiveMoment H raw7346step0 := by
      have heq : raw7346step0 = (fun i j => raw7346 (permutation243 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7346 permutation243 permutation11
    _ = injectiveMoment H node3399 := by rfl

def raw7347 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, -1, 1, -1]]

def raw7347step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, 1, -1, 1]]

def raw7347step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7347 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7347 = injectiveMoment H node3404 := by
  calc
    injectiveMoment H raw7347 = injectiveMoment H raw7347step0 := by
      have heq : raw7347step0 = -raw7347 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7347).symm
    injectiveMoment H raw7347step0 = injectiveMoment H raw7347step1 := by
      have heq : raw7347step1 = (fun i j => raw7347step0 (permutation352 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7347step0 permutation352 permutation11
    _ = injectiveMoment H node3404 := by rfl

def raw7348 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, -1, 1, 0]]

def raw7348step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical7348 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7348 = injectiveMoment H node3450 := by
  calc
    injectiveMoment H raw7348 = injectiveMoment H raw7348step0 := by
      have heq : raw7348step0 = (fun i j => raw7348 (permutation219 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7348 permutation219 permutation27
    _ = injectiveMoment H node3450 := by rfl

def raw7349 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical7349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7349 = injectiveMoment H node1280 := by
  calc
    injectiveMoment H raw7349 = injectiveMoment H raw7349step0 := by
      have heq : raw7349step0 = (fun i j => raw7349 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7349 permutation11 permutation11
    _ = injectiveMoment H node1280 := by rfl

def raw7350 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw7350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 2, 1, -2]]

def raw7350step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical7350 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7350 = injectiveMoment H node1284 := by
  calc
    injectiveMoment H raw7350 = injectiveMoment H raw7350step0 := by
      have heq : raw7350step0 = -raw7350 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7350).symm
    injectiveMoment H raw7350step0 = injectiveMoment H raw7350step1 := by
      have heq : raw7350step1 = (fun i j => raw7350step0 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7350step0 permutation17 permutation21
    _ = injectiveMoment H node1284 := by rfl

def raw7351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, -1, 0, 1], ![-1, 1, 2, -2]]

def raw7351step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical7351 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7351 = injectiveMoment H node1284 := by
  calc
    injectiveMoment H raw7351 = injectiveMoment H raw7351step0 := by
      have heq : raw7351step0 = -raw7351 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7351).symm
    injectiveMoment H raw7351step0 = injectiveMoment H raw7351step1 := by
      have heq : raw7351step1 = (fun i j => raw7351step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7351step0 permutation23 permutation15
    _ = injectiveMoment H node1284 := by rfl

def raw7352 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -3, 2], ![1, -1, 3, -3]]

def raw7352step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -3, 3], ![1, 2, -3]]

def raw7352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, 3, -3], ![-1, -2, 3]]

def raw7352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7352 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7352 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw7352 = injectiveMoment H raw7352step0 := by
      have heq : raw7352step0 = raw7352.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7352).symm
    injectiveMoment H raw7352step0 = injectiveMoment H raw7352step1 := by
      have heq : raw7352step1 = -raw7352step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7352step0).symm
    injectiveMoment H raw7352step1 = injectiveMoment H raw7352step2 := by
      have heq : raw7352step2 = (fun i j => raw7352step1 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7352step1 permutation30 permutation3
    _ = injectiveMoment H node269 := by rfl

def raw7353 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw7353step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2]]

def raw7353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, 2, -2], ![-1, -1, 2]]

def raw7353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7353 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7353 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7353 = injectiveMoment H raw7353step0 := by
      have heq : raw7353step0 = raw7353.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7353).symm
    injectiveMoment H raw7353step0 = injectiveMoment H raw7353step1 := by
      have heq : raw7353step1 = -raw7353step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7353step0).symm
    injectiveMoment H raw7353step1 = injectiveMoment H raw7353step2 := by
      have heq : raw7353step2 = (fun i j => raw7353step1 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7353step1 permutation30 permutation3
    _ = injectiveMoment H node284 := by rfl

def raw7354 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw7354step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw7354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7354 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7354 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw7354 = injectiveMoment H raw7354step0 := by
      have heq : raw7354step0 = raw7354.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7354).symm
    injectiveMoment H raw7354step0 = injectiveMoment H raw7354step1 := by
      have heq : raw7354step1 = (fun i j => raw7354step0 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7354step0 permutation11 permutation3
    _ = injectiveMoment H node293 := by rfl

def raw7355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw7355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 2, 1, -2]]

def raw7355step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical7355 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7355 = injectiveMoment H node1259 := by
  calc
    injectiveMoment H raw7355 = injectiveMoment H raw7355step0 := by
      have heq : raw7355step0 = -raw7355 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7355).symm
    injectiveMoment H raw7355step0 = injectiveMoment H raw7355step1 := by
      have heq : raw7355step1 = (fun i j => raw7355step0 (permutation23 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7355step0 permutation23 permutation21
    _ = injectiveMoment H node1259 := by rfl

def raw7356 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw7356step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2]]

def raw7356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2]]

def raw7356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7356 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7356 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7356 = injectiveMoment H raw7356step0 := by
      have heq : raw7356step0 = raw7356.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7356).symm
    injectiveMoment H raw7356step0 = injectiveMoment H raw7356step1 := by
      have heq : raw7356step1 = -raw7356step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7356step0).symm
    injectiveMoment H raw7356step1 = injectiveMoment H raw7356step2 := by
      have heq : raw7356step2 = (fun i j => raw7356step1 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7356step1 permutation30 permutation4
    _ = injectiveMoment H node272 := by rfl

def raw7357 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -3, 3, -1], ![0, 3, -3, 0]]

def raw7357step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7357 = injectiveMoment H node289 := by
  calc
    injectiveMoment H raw7357 = injectiveMoment H raw7357step0 := by
      have heq : raw7357step0 = raw7357.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7357).symm
    injectiveMoment H raw7357step0 = injectiveMoment H raw7357step1 := by
      have heq : raw7357step1 = (fun i j => raw7357step0 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7357step0 permutation11 permutation4
    _ = injectiveMoment H node289 := by rfl

def raw7358 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 2, -1], ![0, 2, -2, 0]]

def raw7358step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7358 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7358 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7358 = injectiveMoment H raw7358step0 := by
      have heq : raw7358step0 = raw7358.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7358).symm
    injectiveMoment H raw7358step0 = injectiveMoment H raw7358step1 := by
      have heq : raw7358step1 = (fun i j => raw7358step0 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7358step0 permutation11 permutation4
    _ = injectiveMoment H node291 := by rfl

def raw7359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def raw7359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -3, 5]]

def raw7359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem canonical7359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7359 = injectiveMoment H node1382 := by
  calc
    injectiveMoment H raw7359 = injectiveMoment H raw7359step0 := by
      have heq : raw7359step0 = -raw7359 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7359).symm
    injectiveMoment H raw7359step0 = injectiveMoment H raw7359step1 := by
      have heq : raw7359step1 = (fun i j => raw7359step0 (permutation312 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7359step0 permutation312 permutation5
    _ = injectiveMoment H node1382 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
