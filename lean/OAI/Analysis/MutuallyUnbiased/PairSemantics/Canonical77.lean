import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2464 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, -2, 1]]

def raw2464step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical2464 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2464 = injectiveMoment H node846 := by
  calc
    injectiveMoment H raw2464 = injectiveMoment H raw2464step0 := by
      have heq : raw2464step0 = (fun i j => raw2464 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2464 permutation14 permutation15
    _ = injectiveMoment H node846 := by rfl

def raw2465 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw2465step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2465 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2465 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw2465 = injectiveMoment H raw2465step0 := by
      have heq : raw2465step0 = (fun i j => raw2465 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2465 permutation11 permutation9
    _ = injectiveMoment H node510 := by rfl

def raw2466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2466step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical2466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2466 = injectiveMoment H node1826 := by
  calc
    injectiveMoment H raw2466 = injectiveMoment H raw2466step0 := by
      have heq : raw2466step0 = (fun i j => raw2466 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2466 permutation39 permutation9
    _ = injectiveMoment H node1826 := by rfl

def raw2467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2467step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2467 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2467 = injectiveMoment H node1830 := by
  calc
    injectiveMoment H raw2467 = injectiveMoment H raw2467step0 := by
      have heq : raw2467step0 = (fun i j => raw2467 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2467 permutation39 permutation9
    _ = injectiveMoment H node1830 := by rfl

def raw2468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2468step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical2468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2468 = injectiveMoment H node1831 := by
  calc
    injectiveMoment H raw2468 = injectiveMoment H raw2468step0 := by
      have heq : raw2468step0 = (fun i j => raw2468 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2468 permutation39 permutation9
    _ = injectiveMoment H node1831 := by rfl

def raw2469 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw2469step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 1, 0, -2], ![2, -2, -1, 1]]

def raw2469step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2469 = injectiveMoment H node842 := by
  calc
    injectiveMoment H raw2469 = injectiveMoment H raw2469step0 := by
      have heq : raw2469step0 = raw2469.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2469).symm
    injectiveMoment H raw2469step0 = injectiveMoment H raw2469step1 := by
      have heq : raw2469step1 = (fun i j => raw2469step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2469step0 permutation28 permutation24
    _ = injectiveMoment H node842 := by rfl

def raw2470 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical2470 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2470 = injectiveMoment H node514 := by
  rfl

def raw2471 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 1, 0, -2], ![2, -2, 0, 0]]

def raw2471step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, -1, 0, 2], ![-2, 2, 0, 0]]

def raw2471step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical2471 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2471 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw2471 = injectiveMoment H raw2471step0 := by
      have heq : raw2471step0 = raw2471.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2471).symm
    injectiveMoment H raw2471step0 = injectiveMoment H raw2471step1 := by
      have heq : raw2471step1 = -raw2471step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2471step0).symm
    injectiveMoment H raw2471step1 = injectiveMoment H raw2471step2 := by
      have heq : raw2471step2 = (fun i j => raw2471step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2471step1 permutation14 permutation26
    _ = injectiveMoment H node1058 := by rfl

def raw2472 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical2472 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2472 = injectiveMoment H node515 := by
  rfl

def raw2473 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2473step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2473 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2473 = injectiveMoment H node845 := by
  calc
    injectiveMoment H raw2473 = injectiveMoment H raw2473step0 := by
      have heq : raw2473step0 = (fun i j => raw2473 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2473 permutation12 permutation15
    _ = injectiveMoment H node845 := by rfl

def raw2474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 1, -1, -1], ![2, -2, 0, 0]]

def raw2474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![-2, 2, 0, 0]]

def raw2474step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2474 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2474 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw2474 = injectiveMoment H raw2474step0 := by
      have heq : raw2474step0 = raw2474.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2474).symm
    injectiveMoment H raw2474step0 = injectiveMoment H raw2474step1 := by
      have heq : raw2474step1 = -raw2474step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2474step0).symm
    injectiveMoment H raw2474step1 = injectiveMoment H raw2474step2 := by
      have heq : raw2474step2 = (fun i j => raw2474step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2474step1 permutation10 permutation26
    _ = injectiveMoment H node1040 := by rfl

def raw2475 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw2475step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2475 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2475 = injectiveMoment H node845 := by
  calc
    injectiveMoment H raw2475 = injectiveMoment H raw2475step0 := by
      have heq : raw2475step0 = (fun i j => raw2475 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2475 permutation14 permutation15
    _ = injectiveMoment H node845 := by rfl

def raw2476 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def raw2476step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

theorem canonical2476 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2476 = injectiveMoment H node511 := by
  calc
    injectiveMoment H raw2476 = injectiveMoment H raw2476step0 := by
      have heq : raw2476step0 = (fun i j => raw2476 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2476 permutation11 permutation9
    _ = injectiveMoment H node511 := by rfl

def raw2477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -2, 0]]

theorem canonical2477 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2477 = injectiveMoment H node516 := by
  rfl

def raw2478 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw2478step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 2, 0, -3], ![2, -3, 0, 1]]

def raw2478step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, -2, 0, 3], ![-2, 3, 0, -1]]

def raw2478step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 3, -2, -1], ![1, -1, -1, 1]]

theorem canonical2478 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2478 = injectiveMoment H node1018 := by
  calc
    injectiveMoment H raw2478 = injectiveMoment H raw2478step0 := by
      have heq : raw2478step0 = raw2478.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2478).symm
    injectiveMoment H raw2478step0 = injectiveMoment H raw2478step1 := by
      have heq : raw2478step1 = -raw2478step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2478step0).symm
    injectiveMoment H raw2478step1 = injectiveMoment H raw2478step2 := by
      have heq : raw2478step2 = (fun i j => raw2478step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2478step1 permutation14 permutation26
    _ = injectiveMoment H node1018 := by rfl

def raw2479 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, 0, -2, 1], ![1, 0, -1, 0]]

def raw2479step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 2, -2, -1], ![2, -3, 1, 0]]

def raw2479step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical2479 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2479 = injectiveMoment H node836 := by
  calc
    injectiveMoment H raw2479 = injectiveMoment H raw2479step0 := by
      have heq : raw2479step0 = raw2479.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2479).symm
    injectiveMoment H raw2479step0 = injectiveMoment H raw2479step1 := by
      have heq : raw2479step1 = (fun i j => raw2479step0 (permutation24 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2479step0 permutation24 permutation31
    _ = injectiveMoment H node836 := by rfl

def raw2480 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -2, 1]]

def raw2480step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 2, -1, -2], ![2, -3, 0, 1]]

def raw2480step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical2480 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2480 = injectiveMoment H node836 := by
  calc
    injectiveMoment H raw2480 = injectiveMoment H raw2480step0 := by
      have heq : raw2480step0 = raw2480.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2480).symm
    injectiveMoment H raw2480step0 = injectiveMoment H raw2480step1 := by
      have heq : raw2480step1 = (fun i j => raw2480step0 (permutation24 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2480step0 permutation24 permutation25
    _ = injectiveMoment H node836 := by rfl

def raw2481 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw2481step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -3, 0, 2], ![2, 1, 0, -3]]

def raw2481step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 3, 0, -2], ![-2, -1, 0, 3]]

def raw2481step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

theorem canonical2481 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2481 = injectiveMoment H node990 := by
  calc
    injectiveMoment H raw2481 = injectiveMoment H raw2481step0 := by
      have heq : raw2481step0 = raw2481.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2481).symm
    injectiveMoment H raw2481step0 = injectiveMoment H raw2481step1 := by
      have heq : raw2481step1 = -raw2481step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2481step0).symm
    injectiveMoment H raw2481step1 = injectiveMoment H raw2481step2 := by
      have heq : raw2481step2 = (fun i j => raw2481step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2481step1 permutation12 permutation26
    _ = injectiveMoment H node990 := by rfl

def raw2482 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw2482step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -3, 1, 1], ![2, 1, -1, -2]]

def raw2482step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

theorem canonical2482 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2482 = injectiveMoment H node505 := by
  calc
    injectiveMoment H raw2482 = injectiveMoment H raw2482step0 := by
      have heq : raw2482step0 = raw2482.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2482).symm
    injectiveMoment H raw2482step0 = injectiveMoment H raw2482step1 := by
      have heq : raw2482step1 = (fun i j => raw2482step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2482step0 permutation30 permutation32
    _ = injectiveMoment H node505 := by rfl

def raw2483 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw2483step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -3, 2, 0], ![2, 1, -2, -1]]

def raw2483step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

theorem canonical2483 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2483 = injectiveMoment H node823 := by
  calc
    injectiveMoment H raw2483 = injectiveMoment H raw2483step0 := by
      have heq : raw2483step0 = raw2483.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2483).symm
    injectiveMoment H raw2483step0 = injectiveMoment H raw2483step1 := by
      have heq : raw2483step1 = (fun i j => raw2483step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2483step0 permutation30 permutation32
    _ = injectiveMoment H node823 := by rfl

def raw2484 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2484step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -2, -1, 2], ![2, 0, 1, -3]]

def raw2484step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

theorem canonical2484 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2484 = injectiveMoment H node511 := by
  calc
    injectiveMoment H raw2484 = injectiveMoment H raw2484step0 := by
      have heq : raw2484step0 = raw2484.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2484).symm
    injectiveMoment H raw2484step0 = injectiveMoment H raw2484step1 := by
      have heq : raw2484step1 = (fun i j => raw2484step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2484step0 permutation22 permutation17
    _ = injectiveMoment H node511 := by rfl

def raw2485 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -2, 0, 1], ![2, 0, 0, -2]]

def raw2485step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 2, 0, -1], ![-2, 0, 0, 2]]

def raw2485step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical2485 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2485 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw2485 = injectiveMoment H raw2485step0 := by
      have heq : raw2485step0 = raw2485.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2485).symm
    injectiveMoment H raw2485step0 = injectiveMoment H raw2485step1 := by
      have heq : raw2485step1 = -raw2485step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2485step0).symm
    injectiveMoment H raw2485step1 = injectiveMoment H raw2485step2 := by
      have heq : raw2485step2 = (fun i j => raw2485step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2485step1 permutation12 permutation26
    _ = injectiveMoment H node1010 := by rfl

def raw2486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -2, 1, 0], ![2, 0, -1, -1]]

def raw2486step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical2486 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2486 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw2486 = injectiveMoment H raw2486step0 := by
      have heq : raw2486step0 = raw2486.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2486).symm
    injectiveMoment H raw2486step0 = injectiveMoment H raw2486step1 := by
      have heq : raw2486step1 = (fun i j => raw2486step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2486step0 permutation30 permutation32
    _ = injectiveMoment H node1005 := by rfl

def raw2487 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw2487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![1, -2, 0, 1], ![2, 0, -1, -1]]

def raw2487step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical2487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2487 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw2487 = injectiveMoment H raw2487step0 := by
      have heq : raw2487step0 = raw2487.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2487).symm
    injectiveMoment H raw2487step0 = injectiveMoment H raw2487step1 := by
      have heq : raw2487step1 = (fun i j => raw2487step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2487step0 permutation30 permutation26
    _ = injectiveMoment H node1005 := by rfl

def raw2488 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw2488step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw2488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical2488 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2488 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw2488 = injectiveMoment H raw2488step0 := by
      have heq : raw2488step0 = raw2488.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2488).symm
    injectiveMoment H raw2488step0 = injectiveMoment H raw2488step1 := by
      have heq : raw2488step1 = (fun i j => raw2488step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2488step0 permutation22 permutation5
    _ = injectiveMoment H node224 := by rfl

def raw2489 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical2489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2489 = injectiveMoment H node517 := by
  rfl

def raw2490 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2490step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -1, 0, 0], ![2, -1, 0, -1]]

def raw2490step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 1, 0, 0], ![-2, 1, 0, 1]]

def raw2490step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical2490 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2490 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw2490 = injectiveMoment H raw2490step0 := by
      have heq : raw2490step0 = raw2490.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2490).symm
    injectiveMoment H raw2490step0 = injectiveMoment H raw2490step1 := by
      have heq : raw2490step1 = -raw2490step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2490step0).symm
    injectiveMoment H raw2490step1 = injectiveMoment H raw2490step2 := by
      have heq : raw2490step2 = (fun i j => raw2490step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2490step1 permutation11 permutation32
    _ = injectiveMoment H node1047 := by rfl

def raw2491 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2491step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -1, 1, -1], ![2, -1, -1, 0]]

def raw2491step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 1, -1, 1], ![-2, 1, 1, 0]]

def raw2491step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2491 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2491 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw2491 = injectiveMoment H raw2491step0 := by
      have heq : raw2491step0 = raw2491.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2491).symm
    injectiveMoment H raw2491step0 = injectiveMoment H raw2491step1 := by
      have heq : raw2491step1 = -raw2491step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2491step0).symm
    injectiveMoment H raw2491step1 = injectiveMoment H raw2491step2 := by
      have heq : raw2491step2 = (fun i j => raw2491step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2491step1 permutation10 permutation32
    _ = injectiveMoment H node1078 := by rfl

def raw2492 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw2492step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![1, -1, -1, 1], ![2, -1, 0, -1]]

def raw2492step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 0, 1], ![-1, 1, 1, -1], ![-2, 1, 0, 1]]

def raw2492step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2492 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2492 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw2492 = injectiveMoment H raw2492step0 := by
      have heq : raw2492step0 = raw2492.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2492).symm
    injectiveMoment H raw2492step0 = injectiveMoment H raw2492step1 := by
      have heq : raw2492step1 = -raw2492step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2492step0).symm
    injectiveMoment H raw2492step1 = injectiveMoment H raw2492step2 := by
      have heq : raw2492step2 = (fun i j => raw2492step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2492step1 permutation10 permutation26
    _ = injectiveMoment H node1078 := by rfl

def raw2493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 1, -2]]

theorem canonical2493 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2493 = injectiveMoment H node518 := by
  rfl

def raw2494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2494step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 0, -1, 0], ![2, -2, 1, -1]]

def raw2494step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2494 = injectiveMoment H node837 := by
  calc
    injectiveMoment H raw2494 = injectiveMoment H raw2494step0 := by
      have heq : raw2494step0 = raw2494.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2494).symm
    injectiveMoment H raw2494step0 = injectiveMoment H raw2494step1 := by
      have heq : raw2494step1 = (fun i j => raw2494step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2494step0 permutation32 permutation30
    _ = injectiveMoment H node837 := by rfl

def raw2495 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2495step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 0, 0, -1], ![2, -2, 0, 0]]

def raw2495step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 0, 0, 1], ![-2, 2, 0, 0]]

def raw2495step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical2495 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2495 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2495 = injectiveMoment H raw2495step0 := by
      have heq : raw2495step0 = raw2495.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2495).symm
    injectiveMoment H raw2495step0 = injectiveMoment H raw2495step1 := by
      have heq : raw2495step1 = -raw2495step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2495step0).symm
    injectiveMoment H raw2495step1 = injectiveMoment H raw2495step2 := by
      have heq : raw2495step2 = (fun i j => raw2495step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2495step1 permutation13 permutation32
    _ = injectiveMoment H node1053 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
