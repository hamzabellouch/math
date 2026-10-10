import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7296 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw7296step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -2, 4]]

def raw7296step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical7296 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7296 = injectiveMoment H node2879 := by
  calc
    injectiveMoment H raw7296 = injectiveMoment H raw7296step0 := by
      have heq : raw7296step0 = -raw7296 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7296).symm
    injectiveMoment H raw7296step0 = injectiveMoment H raw7296step1 := by
      have heq : raw7296step1 = (fun i j => raw7296step0 (permutation321 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7296step0 permutation321 permutation23
    _ = injectiveMoment H node2879 := by rfl

def raw7297 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw7297step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw7297step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical7297 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7297 = injectiveMoment H node2967 := by
  calc
    injectiveMoment H raw7297 = injectiveMoment H raw7297step0 := by
      have heq : raw7297step0 = -raw7297 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7297).symm
    injectiveMoment H raw7297step0 = injectiveMoment H raw7297step1 := by
      have heq : raw7297step1 = (fun i j => raw7297step0 (permutation399 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7297step0 permutation399 permutation21
    _ = injectiveMoment H node2967 := by rfl

def raw7298 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7298step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -1, -2, 3]]

def raw7298step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical7298 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7298 = injectiveMoment H node3013 := by
  calc
    injectiveMoment H raw7298 = injectiveMoment H raw7298step0 := by
      have heq : raw7298step0 = -raw7298 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7298).symm
    injectiveMoment H raw7298step0 = injectiveMoment H raw7298step1 := by
      have heq : raw7298step1 = (fun i j => raw7298step0 (permutation320 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7298step0 permutation320 permutation23
    _ = injectiveMoment H node3013 := by rfl

def raw7299 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw7299step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw7299step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical7299 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7299 = injectiveMoment H node2928 := by
  calc
    injectiveMoment H raw7299 = injectiveMoment H raw7299step0 := by
      have heq : raw7299step0 = -raw7299 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7299).symm
    injectiveMoment H raw7299step0 = injectiveMoment H raw7299step1 := by
      have heq : raw7299step1 = (fun i j => raw7299step0 (permutation338 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7299step0 permutation338 permutation21
    _ = injectiveMoment H node2928 := by rfl

def raw7300 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 1, 2, -4]]

def raw7300step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, -1, -2, 4]]

def raw7300step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical7300 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7300 = injectiveMoment H node3334 := by
  calc
    injectiveMoment H raw7300 = injectiveMoment H raw7300step0 := by
      have heq : raw7300step0 = -raw7300 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7300).symm
    injectiveMoment H raw7300step0 = injectiveMoment H raw7300step1 := by
      have heq : raw7300step1 = (fun i j => raw7300step0 (permutation340 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7300step0 permutation340 permutation11
    _ = injectiveMoment H node3334 := by rfl

def raw7301 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7301step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical7301 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7301 = injectiveMoment H node3440 := by
  calc
    injectiveMoment H raw7301 = injectiveMoment H raw7301step0 := by
      have heq : raw7301step0 = (fun i j => raw7301 (permutation152 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7301 permutation152 permutation9
    _ = injectiveMoment H node3440 := by rfl

def raw7302 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw7302step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw7302step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical7302 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7302 = injectiveMoment H node2910 := by
  calc
    injectiveMoment H raw7302 = injectiveMoment H raw7302step0 := by
      have heq : raw7302step0 = -raw7302 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7302).symm
    injectiveMoment H raw7302step0 = injectiveMoment H raw7302step1 := by
      have heq : raw7302step1 = (fun i j => raw7302step0 (permutation361 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7302step0 permutation361 permutation11
    _ = injectiveMoment H node2910 := by rfl

def raw7303 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw7303step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw7303step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical7303 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7303 = injectiveMoment H node2965 := by
  calc
    injectiveMoment H raw7303 = injectiveMoment H raw7303step0 := by
      have heq : raw7303step0 = -raw7303 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7303).symm
    injectiveMoment H raw7303step0 = injectiveMoment H raw7303step1 := by
      have heq : raw7303step1 = (fun i j => raw7303step0 (permutation361 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7303step0 permutation361 permutation11
    _ = injectiveMoment H node2965 := by rfl

def raw7304 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw7304step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw7304step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical7304 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7304 = injectiveMoment H node3356 := by
  calc
    injectiveMoment H raw7304 = injectiveMoment H raw7304step0 := by
      have heq : raw7304step0 = -raw7304 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7304).symm
    injectiveMoment H raw7304step0 = injectiveMoment H raw7304step1 := by
      have heq : raw7304step1 = (fun i j => raw7304step0 (permutation358 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7304step0 permutation358 permutation21
    _ = injectiveMoment H node3356 := by rfl

def raw7305 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![2, 1, 1, -4]]

def raw7305step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-2, -1, -1, 4]]

def raw7305step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical7305 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7305 = injectiveMoment H node2914 := by
  calc
    injectiveMoment H raw7305 = injectiveMoment H raw7305step0 := by
      have heq : raw7305step0 = -raw7305 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7305).symm
    injectiveMoment H raw7305step0 = injectiveMoment H raw7305step1 := by
      have heq : raw7305step1 = (fun i j => raw7305step0 (permutation359 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7305step0 permutation359 permutation11
    _ = injectiveMoment H node2914 := by rfl

def raw7306 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw7306step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, -1, -1, 3]]

def raw7306step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical7306 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7306 = injectiveMoment H node3373 := by
  calc
    injectiveMoment H raw7306 = injectiveMoment H raw7306step0 := by
      have heq : raw7306step0 = -raw7306 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7306).symm
    injectiveMoment H raw7306step0 = injectiveMoment H raw7306step1 := by
      have heq : raw7306step1 = (fun i j => raw7306step0 (permutation409 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7306step0 permutation409 permutation9
    _ = injectiveMoment H node3373 := by rfl

def raw7307 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![2, 0, 1, -3]]

def raw7307step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![1, -1, 1, -1], ![-2, 0, -1, 3]]

def raw7307step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical7307 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7307 = injectiveMoment H node2965 := by
  calc
    injectiveMoment H raw7307 = injectiveMoment H raw7307step0 := by
      have heq : raw7307step0 = -raw7307 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7307).symm
    injectiveMoment H raw7307step0 = injectiveMoment H raw7307step1 := by
      have heq : raw7307step1 = (fun i j => raw7307step0 (permutation359 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7307step0 permutation359 permutation11
    _ = injectiveMoment H node2965 := by rfl

def raw7308 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 1, 1, -3]]

def raw7308step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, -1, -1, 3]]

def raw7308step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical7308 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7308 = injectiveMoment H node3373 := by
  calc
    injectiveMoment H raw7308 = injectiveMoment H raw7308step0 := by
      have heq : raw7308step0 = -raw7308 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7308).symm
    injectiveMoment H raw7308step0 = injectiveMoment H raw7308step1 := by
      have heq : raw7308step1 = (fun i j => raw7308step0 (permutation394 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7308step0 permutation394 permutation9
    _ = injectiveMoment H node3373 := by rfl

def raw7309 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7309step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 0, -1, 2]]

def raw7309step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7309 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7309 = injectiveMoment H node3393 := by
  calc
    injectiveMoment H raw7309 = injectiveMoment H raw7309step0 := by
      have heq : raw7309step0 = -raw7309 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7309).symm
    injectiveMoment H raw7309step0 = injectiveMoment H raw7309step1 := by
      have heq : raw7309step1 = (fun i j => raw7309step0 (permutation360 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7309step0 permutation360 permutation11
    _ = injectiveMoment H node3393 := by rfl

def raw7310 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![0, 1, 1, -2]]

def raw7310step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical7310 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7310 = injectiveMoment H node3442 := by
  calc
    injectiveMoment H raw7310 = injectiveMoment H raw7310step0 := by
      have heq : raw7310step0 = (fun i j => raw7310 (permutation152 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7310 permutation152 permutation9
    _ = injectiveMoment H node3442 := by rfl

def raw7311 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw7311step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw7311step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical7311 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7311 = injectiveMoment H node2866 := by
  calc
    injectiveMoment H raw7311 = injectiveMoment H raw7311step0 := by
      have heq : raw7311step0 = -raw7311 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7311).symm
    injectiveMoment H raw7311step0 = injectiveMoment H raw7311step1 := by
      have heq : raw7311step1 = (fun i j => raw7311step0 (permutation326 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7311step0 permutation326 permutation23
    _ = injectiveMoment H node2866 := by rfl

def raw7312 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw7312step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw7312step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical7312 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7312 = injectiveMoment H node2914 := by
  calc
    injectiveMoment H raw7312 = injectiveMoment H raw7312step0 := by
      have heq : raw7312step0 = -raw7312 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7312).symm
    injectiveMoment H raw7312step0 = injectiveMoment H raw7312step1 := by
      have heq : raw7312step1 = (fun i j => raw7312step0 (permutation398 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7312step0 permutation398 permutation21
    _ = injectiveMoment H node2914 := by rfl

def raw7313 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw7313step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical7313 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7313 = injectiveMoment H node3439 := by
  calc
    injectiveMoment H raw7313 = injectiveMoment H raw7313step0 := by
      have heq : raw7313step0 = (fun i j => raw7313 (permutation157 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7313 permutation157 permutation9
    _ = injectiveMoment H node3439 := by rfl

def raw7314 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 2, 2, -5]]

def raw7314step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, -2, -2, 5]]

def raw7314step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical7314 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7314 = injectiveMoment H node3330 := by
  calc
    injectiveMoment H raw7314 = injectiveMoment H raw7314step0 := by
      have heq : raw7314step0 = -raw7314 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7314).symm
    injectiveMoment H raw7314step0 = injectiveMoment H raw7314step1 := by
      have heq : raw7314step1 = (fun i j => raw7314step0 (permutation365 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7314step0 permutation365 permutation9
    _ = injectiveMoment H node3330 := by rfl

def raw7315 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7315step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical7315 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7315 = injectiveMoment H node3439 := by
  calc
    injectiveMoment H raw7315 = injectiveMoment H raw7315step0 := by
      have heq : raw7315step0 = (fun i j => raw7315 (permutation170 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7315 permutation170 permutation11
    _ = injectiveMoment H node3439 := by rfl

def raw7316 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 1, 2, -4]]

def raw7316step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, -1, -2, 4]]

def raw7316step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical7316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7316 = injectiveMoment H node3334 := by
  calc
    injectiveMoment H raw7316 = injectiveMoment H raw7316step0 := by
      have heq : raw7316step0 = -raw7316 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7316).symm
    injectiveMoment H raw7316step0 = injectiveMoment H raw7316step1 := by
      have heq : raw7316step1 = (fun i j => raw7316step0 (permutation354 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7316step0 permutation354 permutation11
    _ = injectiveMoment H node3334 := by rfl

def raw7317 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7317step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical7317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7317 = injectiveMoment H node3441 := by
  calc
    injectiveMoment H raw7317 = injectiveMoment H raw7317step0 := by
      have heq : raw7317step0 = (fun i j => raw7317 (permutation170 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7317 permutation170 permutation11
    _ = injectiveMoment H node3441 := by rfl

def raw7318 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 0, -1, 1], ![0, 2, 2, -4]]

def raw7318step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical7318 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7318 = injectiveMoment H node3439 := by
  calc
    injectiveMoment H raw7318 = injectiveMoment H raw7318step0 := by
      have heq : raw7318step0 = (fun i j => raw7318 (permutation173 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7318 permutation173 permutation11
    _ = injectiveMoment H node3439 := by rfl

def raw7319 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 2, 2, -3]]

def raw7319step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, -2, -2, 3]]

def raw7319step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical7319 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7319 = injectiveMoment H node2889 := by
  calc
    injectiveMoment H raw7319 = injectiveMoment H raw7319step0 := by
      have heq : raw7319step0 = -raw7319 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7319).symm
    injectiveMoment H raw7319step0 = injectiveMoment H raw7319step1 := by
      have heq : raw7319step1 = (fun i j => raw7319step0 (permutation328 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7319step0 permutation328 permutation17
    _ = injectiveMoment H node2889 := by rfl

def raw7320 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw7320step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw7320step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical7320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7320 = injectiveMoment H node2967 := by
  calc
    injectiveMoment H raw7320 = injectiveMoment H raw7320step0 := by
      have heq : raw7320step0 = -raw7320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7320).symm
    injectiveMoment H raw7320step0 = injectiveMoment H raw7320step1 := by
      have heq : raw7320step1 = (fun i j => raw7320step0 (permutation398 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7320step0 permutation398 permutation21
    _ = injectiveMoment H node2967 := by rfl

def raw7321 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7321step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical7321 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7321 = injectiveMoment H node3440 := by
  calc
    injectiveMoment H raw7321 = injectiveMoment H raw7321step0 := by
      have heq : raw7321step0 = (fun i j => raw7321 (permutation157 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7321 permutation157 permutation9
    _ = injectiveMoment H node3440 := by rfl

def raw7322 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 0, 2, -3]]

def raw7322step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, 0, -2, 3]]

def raw7322step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7322 = injectiveMoment H node3337 := by
  calc
    injectiveMoment H raw7322 = injectiveMoment H raw7322step0 := by
      have heq : raw7322step0 = -raw7322 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7322).symm
    injectiveMoment H raw7322step0 = injectiveMoment H raw7322step1 := by
      have heq : raw7322step1 = (fun i j => raw7322step0 (permutation352 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7322step0 permutation352 permutation11
    _ = injectiveMoment H node3337 := by rfl

def raw7323 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 0, 2, -2]]

def raw7323step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![0, 0, -2, 2]]

def raw7323step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical7323 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7323 = injectiveMoment H node3437 := by
  calc
    injectiveMoment H raw7323 = injectiveMoment H raw7323step0 := by
      have heq : raw7323step0 = -raw7323 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7323).symm
    injectiveMoment H raw7323step0 = injectiveMoment H raw7323step1 := by
      have heq : raw7323step1 = (fun i j => raw7323step0 (permutation300 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7323step0 permutation300 permutation12
    _ = injectiveMoment H node3437 := by rfl

def raw7324 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 0, -1, 1], ![0, 1, 2, -3]]

def raw7324step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical7324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7324 = injectiveMoment H node3441 := by
  calc
    injectiveMoment H raw7324 = injectiveMoment H raw7324step0 := by
      have heq : raw7324step0 = (fun i j => raw7324 (permutation187 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7324 permutation187 permutation11
    _ = injectiveMoment H node3441 := by rfl

def raw7325 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 1, 2, -2]]

def raw7325step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical7325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7325 = injectiveMoment H node3083 := by
  calc
    injectiveMoment H raw7325 = injectiveMoment H raw7325step0 := by
      have heq : raw7325step0 = (fun i j => raw7325 (permutation366 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7325 permutation366 permutation27
    _ = injectiveMoment H node3083 := by rfl

def raw7326 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 1, -1, -1]]

def raw7326step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -3, 2], ![0, 0, 2, -2], ![-1, -1, 1, 1]]

def raw7326step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical7326 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7326 = injectiveMoment H node1109 := by
  calc
    injectiveMoment H raw7326 = injectiveMoment H raw7326step0 := by
      have heq : raw7326step0 = -raw7326 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7326).symm
    injectiveMoment H raw7326step0 = injectiveMoment H raw7326step1 := by
      have heq : raw7326step1 = (fun i j => raw7326step0 (permutation31 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7326step0 permutation31 permutation16
    _ = injectiveMoment H node1109 := by rfl

def raw7327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw7327step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical7327 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7327 = injectiveMoment H node1201 := by
  calc
    injectiveMoment H raw7327 = injectiveMoment H raw7327step0 := by
      have heq : raw7327step0 = (fun i j => raw7327 (permutation16 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7327 permutation16 permutation16
    _ = injectiveMoment H node1201 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
