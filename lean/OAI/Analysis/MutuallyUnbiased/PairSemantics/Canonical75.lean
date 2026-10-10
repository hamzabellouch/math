import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2400 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical2400 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2400 = injectiveMoment H node1821 := by
  rfl

def raw2401 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

theorem canonical2401 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2401 = injectiveMoment H node511 := by
  rfl

def raw2402 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical2402 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2402 = injectiveMoment H node512 := by
  rfl

def raw2403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -2, 0, 1], ![2, 1, 0, -3]]

def raw2403step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, 2, 0, -1], ![-2, -1, 0, 3]]

def raw2403step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical2403 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2403 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw2403 = injectiveMoment H raw2403step0 := by
      have heq : raw2403step0 = raw2403.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2403).symm
    injectiveMoment H raw2403step0 = injectiveMoment H raw2403step1 := by
      have heq : raw2403step1 = -raw2403step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2403step0).symm
    injectiveMoment H raw2403step1 = injectiveMoment H raw2403step2 := by
      have heq : raw2403step2 = (fun i j => raw2403step1 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2403step1 permutation14 permutation24
    _ = injectiveMoment H node1249 := by rfl

def raw2404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical2404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2404 = injectiveMoment H node513 := by
  rfl

def raw2405 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw2405step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical2405 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2405 = injectiveMoment H node850 := by
  calc
    injectiveMoment H raw2405 = injectiveMoment H raw2405step0 := by
      have heq : raw2405step0 = (fun i j => raw2405 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2405 permutation12 permutation15
    _ = injectiveMoment H node850 := by rfl

def raw2406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -2, 0, 1], ![2, 1, -1, -2]]

def raw2406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical2406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2406 = injectiveMoment H node838 := by
  calc
    injectiveMoment H raw2406 = injectiveMoment H raw2406step0 := by
      have heq : raw2406step0 = raw2406.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2406).symm
    injectiveMoment H raw2406step0 = injectiveMoment H raw2406step1 := by
      have heq : raw2406step1 = (fun i j => raw2406step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2406step0 permutation30 permutation26
    _ = injectiveMoment H node838 := by rfl

def raw2407 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw2407step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![2, 1, -2, -1]]

def raw2407step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical2407 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2407 = injectiveMoment H node838 := by
  calc
    injectiveMoment H raw2407 = injectiveMoment H raw2407step0 := by
      have heq : raw2407step0 = raw2407.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2407).symm
    injectiveMoment H raw2407step0 = injectiveMoment H raw2407step1 := by
      have heq : raw2407step1 = (fun i j => raw2407step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2407step0 permutation30 permutation32
    _ = injectiveMoment H node838 := by rfl

def raw2408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw2408step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical2408 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2408 = injectiveMoment H node850 := by
  calc
    injectiveMoment H raw2408 = injectiveMoment H raw2408step0 := by
      have heq : raw2408step0 = (fun i j => raw2408 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2408 permutation14 permutation15
    _ = injectiveMoment H node850 := by rfl

def raw2409 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2409step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![1, -1, 0, -1, 1], ![2, 0, 0, 0, -2]]

def raw2409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw2409step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2409 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw2409 = injectiveMoment H raw2409step0 := by
      have heq : raw2409step0 = raw2409.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2409).symm
    injectiveMoment H raw2409step0 = injectiveMoment H raw2409step1 := by
      have hz : ∀ i, raw2409step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2409step1 = (fun i j => raw2409step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2409step0 permutation80 hz
    injectiveMoment H raw2409step1 = injectiveMoment H raw2409step2 := by
      have heq : raw2409step2 = (fun i j => raw2409step1 (permutation26 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2409step1 permutation26 permutation24
    _ = injectiveMoment H node1110 := by rfl

def raw2410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2410step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![1, -1, 0, 0, 0], ![2, 0, 0, -1, -1]]

def raw2410step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw2410step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical2410 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2410 = injectiveMoment H node1039 := by
  calc
    injectiveMoment H raw2410 = injectiveMoment H raw2410step0 := by
      have heq : raw2410step0 = raw2410.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2410).symm
    injectiveMoment H raw2410step0 = injectiveMoment H raw2410step1 := by
      have hz : ∀ i, raw2410step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2410step1 = (fun i j => raw2410step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2410step0 permutation80 hz
    injectiveMoment H raw2410step1 = injectiveMoment H raw2410step2 := by
      have heq : raw2410step2 = (fun i j => raw2410step1 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2410step1 permutation32 permutation26
    _ = injectiveMoment H node1039 := by rfl

def raw2411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 0, -2]]

def raw2411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![2, 0, 0, -2]]

def raw2411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw2411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical2411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2411 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw2411 = injectiveMoment H raw2411step0 := by
      have heq : raw2411step0 = raw2411.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2411).symm
    injectiveMoment H raw2411step0 = injectiveMoment H raw2411step1 := by
      have hz : ∀ i, raw2411step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw2411step1 = (fun i j => raw2411step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2411step0 permutation21 hz
    injectiveMoment H raw2411step1 = injectiveMoment H raw2411step2 := by
      have heq : raw2411step2 = (fun i j => raw2411step1 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2411step1 permutation25 permutation6
    _ = injectiveMoment H node291 := by rfl

def raw2412 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2412step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical2412 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2412 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw2412 = injectiveMoment H raw2412step0 := by
      have heq : raw2412step0 = (fun i j => raw2412 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2412 permutation42 permutation15
    _ = injectiveMoment H node2449 := by rfl

def raw2413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw2413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![2, 0, -1, -1]]

def raw2413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical2413 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2413 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw2413 = injectiveMoment H raw2413step0 := by
      have heq : raw2413step0 = raw2413.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2413).symm
    injectiveMoment H raw2413step0 = injectiveMoment H raw2413step1 := by
      have heq : raw2413step1 = (fun i j => raw2413step0 (permutation27 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2413step0 permutation27 permutation24
    _ = injectiveMoment H node1265 := by rfl

def raw2414 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -1, 2, -3]]

def raw2414step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, -2, 2], ![2, 0, 1, -3]]

def raw2414step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical2414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2414 = injectiveMoment H node829 := by
  calc
    injectiveMoment H raw2414 = injectiveMoment H raw2414step0 := by
      have heq : raw2414step0 = raw2414.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2414).symm
    injectiveMoment H raw2414step0 = injectiveMoment H raw2414step1 := by
      have heq : raw2414step1 = (fun i j => raw2414step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2414step0 permutation22 permutation17
    _ = injectiveMoment H node829 := by rfl

def raw2415 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem canonical2415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2415 = injectiveMoment H node1822 := by
  rfl

def raw2416 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2416step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2416step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical2416 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2416 = injectiveMoment H node1785 := by
  calc
    injectiveMoment H raw2416 = injectiveMoment H raw2416step0 := by
      have heq : raw2416step0 = -raw2416 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2416).symm
    injectiveMoment H raw2416step0 = injectiveMoment H raw2416step1 := by
      have heq : raw2416step1 = (fun i j => raw2416step0 (permutation45 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2416step0 permutation45 permutation32
    _ = injectiveMoment H node1785 := by rfl

def raw2417 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2417 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2417 = injectiveMoment H node1823 := by
  rfl

def raw2418 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw2418step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2418 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2418 = injectiveMoment H node1823 := by
  calc
    injectiveMoment H raw2418 = injectiveMoment H raw2418step0 := by
      have heq : raw2418step0 = (fun i j => raw2418 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2418 permutation34 permutation9
    _ = injectiveMoment H node1823 := by rfl

def raw2419 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw2419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2419 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2419 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw2419 = injectiveMoment H raw2419step0 := by
      have heq : raw2419step0 = raw2419.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2419).symm
    injectiveMoment H raw2419step0 = injectiveMoment H raw2419step1 := by
      have heq : raw2419step1 = (fun i j => raw2419step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2419step0 permutation22 permutation17
    _ = injectiveMoment H node1107 := by rfl

def raw2420 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical2420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2420 = injectiveMoment H node1824 := by
  rfl

def raw2421 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2421step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2421step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical2421 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2421 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw2421 = injectiveMoment H raw2421step0 := by
      have heq : raw2421step0 = -raw2421 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2421).symm
    injectiveMoment H raw2421step0 = injectiveMoment H raw2421step1 := by
      have heq : raw2421step1 = (fun i j => raw2421step0 (permutation48 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2421step0 permutation48 permutation26
    _ = injectiveMoment H node2449 := by rfl

def raw2422 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2422 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2422 = injectiveMoment H node1825 := by
  rfl

def raw2423 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw2423step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2423 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2423 = injectiveMoment H node1825 := by
  calc
    injectiveMoment H raw2423 = injectiveMoment H raw2423step0 := by
      have heq : raw2423step0 = (fun i j => raw2423 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2423 permutation34 permutation9
    _ = injectiveMoment H node1825 := by rfl

def raw2424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw2424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-1, 1, 0, 0], ![-2, 0, 1, 1]]

def raw2424step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2424 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2424 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw2424 = injectiveMoment H raw2424step0 := by
      have heq : raw2424step0 = raw2424.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2424).symm
    injectiveMoment H raw2424step0 = injectiveMoment H raw2424step1 := by
      have heq : raw2424step1 = -raw2424step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2424step0).symm
    injectiveMoment H raw2424step1 = injectiveMoment H raw2424step2 := by
      have heq : raw2424step2 = (fun i j => raw2424step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2424step1 permutation15 permutation24
    _ = injectiveMoment H node1110 := by rfl

def raw2425 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical2425 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2425 = injectiveMoment H node1826 := by
  rfl

def raw2426 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2426step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2426step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical2426 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2426 = injectiveMoment H node1786 := by
  calc
    injectiveMoment H raw2426 = injectiveMoment H raw2426step0 := by
      have heq : raw2426step0 = -raw2426 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2426).symm
    injectiveMoment H raw2426step0 = injectiveMoment H raw2426step1 := by
      have heq : raw2426step1 = (fun i j => raw2426step0 (permutation46 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2426step0 permutation46 permutation32
    _ = injectiveMoment H node1786 := by rfl

def raw2427 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2427step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw2427step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical2427 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2427 = injectiveMoment H node1786 := by
  calc
    injectiveMoment H raw2427 = injectiveMoment H raw2427step0 := by
      have heq : raw2427step0 = -raw2427 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2427).symm
    injectiveMoment H raw2427step0 = injectiveMoment H raw2427step1 := by
      have heq : raw2427step1 = (fun i j => raw2427step0 (permutation52 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2427step0 permutation52 permutation32
    _ = injectiveMoment H node1786 := by rfl

def raw2428 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2428step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![2, 0, -2, 0]]

def raw2428step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical2428 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2428 = injectiveMoment H node1112 := by
  calc
    injectiveMoment H raw2428 = injectiveMoment H raw2428step0 := by
      have heq : raw2428step0 = raw2428.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2428).symm
    injectiveMoment H raw2428step0 = injectiveMoment H raw2428step1 := by
      have heq : raw2428step1 = (fun i j => raw2428step0 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2428step0 permutation25 permutation20
    _ = injectiveMoment H node1112 := by rfl

def raw2429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2429 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2429 = injectiveMoment H node1827 := by
  rfl

def raw2430 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical2430 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2430 = injectiveMoment H node1828 := by
  rfl

def raw2431 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, -2, 1]]

def raw2431step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![2, 0, -3, 1]]

def raw2431step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 2, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

theorem canonical2431 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2431 = injectiveMoment H node852 := by
  calc
    injectiveMoment H raw2431 = injectiveMoment H raw2431step0 := by
      have heq : raw2431step0 = raw2431.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2431).symm
    injectiveMoment H raw2431step0 = injectiveMoment H raw2431step1 := by
      have heq : raw2431step1 = (fun i j => raw2431step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2431step0 permutation25 permutation19
    _ = injectiveMoment H node852 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
