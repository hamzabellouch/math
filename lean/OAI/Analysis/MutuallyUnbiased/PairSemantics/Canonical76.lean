import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2432 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw2432step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, -2, 2], ![2, 0, 2, -4]]

def raw2432step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical2432 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2432 = injectiveMoment H node849 := by
  calc
    injectiveMoment H raw2432 = injectiveMoment H raw2432step0 := by
      have heq : raw2432step0 = raw2432.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2432).symm
    injectiveMoment H raw2432step0 = injectiveMoment H raw2432step1 := by
      have heq : raw2432step1 = (fun i j => raw2432step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2432step0 permutation22 permutation17
    _ = injectiveMoment H node849 := by rfl

def raw2433 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2433step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![2, 0, 1, -3]]

def raw2433step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2433 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2433 = injectiveMoment H node1123 := by
  calc
    injectiveMoment H raw2433 = injectiveMoment H raw2433step0 := by
      have heq : raw2433step0 = raw2433.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2433).symm
    injectiveMoment H raw2433step0 = injectiveMoment H raw2433step1 := by
      have heq : raw2433step1 = (fun i j => raw2433step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2433step0 permutation25 permutation18
    _ = injectiveMoment H node1123 := by rfl

def raw2434 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2434step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![2, 0, 0, -2]]

def raw2434step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-2, 0, 0, 2]]

def raw2434step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical2434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2434 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw2434 = injectiveMoment H raw2434step0 := by
      have heq : raw2434step0 = raw2434.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2434).symm
    injectiveMoment H raw2434step0 = injectiveMoment H raw2434step1 := by
      have heq : raw2434step1 = -raw2434step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2434step0).symm
    injectiveMoment H raw2434step1 = injectiveMoment H raw2434step2 := by
      have heq : raw2434step2 = (fun i j => raw2434step1 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2434step1 permutation14 permutation24
    _ = injectiveMoment H node1265 := by rfl

def raw2435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2435step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![2, 0, -1, -1]]

def raw2435step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical2435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2435 = injectiveMoment H node1096 := by
  calc
    injectiveMoment H raw2435 = injectiveMoment H raw2435step0 := by
      have heq : raw2435step0 = raw2435.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2435).symm
    injectiveMoment H raw2435step0 = injectiveMoment H raw2435step1 := by
      have heq : raw2435step1 = (fun i j => raw2435step0 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2435step0 permutation25 permutation20
    _ = injectiveMoment H node1096 := by rfl

def raw2436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 0, 2, -3]]

def raw2436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical2436 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2436 = injectiveMoment H node847 := by
  calc
    injectiveMoment H raw2436 = injectiveMoment H raw2436step0 := by
      have heq : raw2436step0 = (fun i j => raw2436 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2436 permutation12 permutation15
    _ = injectiveMoment H node847 := by rfl

def raw2437 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2437step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw2437step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2437 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2437 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw2437 = injectiveMoment H raw2437step0 := by
      have heq : raw2437step0 = raw2437.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2437).symm
    injectiveMoment H raw2437step0 = injectiveMoment H raw2437step1 := by
      have heq : raw2437step1 = (fun i j => raw2437step0 (permutation26 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2437step0 permutation26 permutation24
    _ = injectiveMoment H node1110 := by rfl

def raw2438 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2438step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw2438step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical2438 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2438 = injectiveMoment H node1039 := by
  calc
    injectiveMoment H raw2438 = injectiveMoment H raw2438step0 := by
      have heq : raw2438step0 = raw2438.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2438).symm
    injectiveMoment H raw2438step0 = injectiveMoment H raw2438step1 := by
      have heq : raw2438step1 = (fun i j => raw2438step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2438step0 permutation32 permutation26
    _ = injectiveMoment H node1039 := by rfl

def raw2439 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2439step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical2439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2439 = injectiveMoment H node2447 := by
  calc
    injectiveMoment H raw2439 = injectiveMoment H raw2439step0 := by
      have heq : raw2439step0 = (fun i j => raw2439 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2439 permutation42 permutation15
    _ = injectiveMoment H node2447 := by rfl

def raw2440 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2440step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical2440 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2440 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw2440 = injectiveMoment H raw2440step0 := by
      have heq : raw2440step0 = (fun i j => raw2440 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2440 permutation42 permutation15
    _ = injectiveMoment H node2448 := by rfl

def raw2441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -2, 0]]

def raw2441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![2, -1, -1, 0]]

def raw2441step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical2441 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2441 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2441 = injectiveMoment H raw2441step0 := by
      have heq : raw2441step0 = raw2441.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2441).symm
    injectiveMoment H raw2441step0 = injectiveMoment H raw2441step1 := by
      have heq : raw2441step1 = (fun i j => raw2441step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2441step0 permutation28 permutation18
    _ = injectiveMoment H node1053 := by rfl

def raw2442 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2442step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical2442 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2442 = injectiveMoment H node1824 := by
  calc
    injectiveMoment H raw2442 = injectiveMoment H raw2442step0 := by
      have heq : raw2442step0 = (fun i j => raw2442 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2442 permutation39 permutation9
    _ = injectiveMoment H node1824 := by rfl

def raw2443 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2443step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2443step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical2443 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2443 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw2443 = injectiveMoment H raw2443step0 := by
      have heq : raw2443step0 = -raw2443 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2443).symm
    injectiveMoment H raw2443step0 = injectiveMoment H raw2443step1 := by
      have heq : raw2443step1 = (fun i j => raw2443step0 (permutation46 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2443step0 permutation46 permutation26
    _ = injectiveMoment H node2449 := by rfl

def raw2444 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2444step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2444 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2444 = injectiveMoment H node1825 := by
  calc
    injectiveMoment H raw2444 = injectiveMoment H raw2444step0 := by
      have heq : raw2444step0 = (fun i j => raw2444 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2444 permutation39 permutation9
    _ = injectiveMoment H node1825 := by rfl

def raw2445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 0, -1, 0], ![2, -1, 0, -1]]

def raw2445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-1, 0, 1, 0], ![-2, 1, 0, 1]]

def raw2445step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2445 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2445 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw2445 = injectiveMoment H raw2445step0 := by
      have heq : raw2445step0 = raw2445.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2445).symm
    injectiveMoment H raw2445step0 = injectiveMoment H raw2445step1 := by
      have heq : raw2445step1 = -raw2445step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2445step0).symm
    injectiveMoment H raw2445step1 = injectiveMoment H raw2445step2 := by
      have heq : raw2445step2 = (fun i j => raw2445step1 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2445step1 permutation15 permutation18
    _ = injectiveMoment H node1110 := by rfl

def raw2446 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2446step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical2446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2446 = injectiveMoment H node2647 := by
  calc
    injectiveMoment H raw2446 = injectiveMoment H raw2446step0 := by
      have heq : raw2446step0 = (fun i j => raw2446 (permutation125 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2446 permutation125 permutation23
    _ = injectiveMoment H node2647 := by rfl

def raw2447 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2447step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2447step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical2447 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2447 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw2447 = injectiveMoment H raw2447step0 := by
      have heq : raw2447step0 = -raw2447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2447).symm
    injectiveMoment H raw2447step0 = injectiveMoment H raw2447step1 := by
      have heq : raw2447step1 = (fun i j => raw2447step0 (permutation45 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2447step0 permutation45 permutation26
    _ = injectiveMoment H node2448 := by rfl

def raw2448 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

theorem canonical2448 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2448 = injectiveMoment H node1829 := by
  rfl

def raw2449 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw2449step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

theorem canonical2449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2449 = injectiveMoment H node1829 := by
  calc
    injectiveMoment H raw2449 = injectiveMoment H raw2449step0 := by
      have heq : raw2449step0 = (fun i j => raw2449 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2449 permutation34 permutation9
    _ = injectiveMoment H node1829 := by rfl

def raw2450 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2450step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw2450step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical2450 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2450 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw2450 = injectiveMoment H raw2450step0 := by
      have heq : raw2450step0 = -raw2450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2450).symm
    injectiveMoment H raw2450step0 = injectiveMoment H raw2450step1 := by
      have heq : raw2450step1 = (fun i j => raw2450step0 (permutation51 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2450step0 permutation51 permutation26
    _ = injectiveMoment H node2448 := by rfl

def raw2451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![2, -1, -1, 0]]

def raw2451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2451 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw2451 = injectiveMoment H raw2451step0 := by
      have heq : raw2451step0 = raw2451.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2451).symm
    injectiveMoment H raw2451step0 = injectiveMoment H raw2451step1 := by
      have heq : raw2451step1 = (fun i j => raw2451step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2451step0 permutation31 permutation18
    _ = injectiveMoment H node1040 := by rfl

def raw2452 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2452 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2452 = injectiveMoment H node1830 := by
  rfl

def raw2453 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical2453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2453 = injectiveMoment H node1831 := by
  rfl

def raw2454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2454 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2454 = injectiveMoment H node1830 := by
  calc
    injectiveMoment H raw2454 = injectiveMoment H raw2454step0 := by
      have heq : raw2454step0 = (fun i j => raw2454 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2454 permutation34 permutation9
    _ = injectiveMoment H node1830 := by rfl

def raw2455 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw2455step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![2, -1, -2, 1]]

def raw2455step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2455 = injectiveMoment H node842 := by
  calc
    injectiveMoment H raw2455 = injectiveMoment H raw2455step0 := by
      have heq : raw2455step0 = raw2455.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2455).symm
    injectiveMoment H raw2455step0 = injectiveMoment H raw2455step1 := by
      have heq : raw2455step1 = (fun i j => raw2455step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2455step0 permutation28 permutation18
    _ = injectiveMoment H node842 := by rfl

def raw2456 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw2456step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, -2, 1], ![2, -1, 2, -3]]

def raw2456step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical2456 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2456 = injectiveMoment H node730 := by
  calc
    injectiveMoment H raw2456 = injectiveMoment H raw2456step0 := by
      have heq : raw2456step0 = raw2456.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2456).symm
    injectiveMoment H raw2456step0 = injectiveMoment H raw2456step1 := by
      have heq : raw2456step1 = (fun i j => raw2456step0 (permutation28 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2456step0 permutation28 permutation19
    _ = injectiveMoment H node730 := by rfl

def raw2457 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw2457step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![2, -1, 1, -2]]

def raw2457step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical2457 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2457 = injectiveMoment H node835 := by
  calc
    injectiveMoment H raw2457 = injectiveMoment H raw2457step0 := by
      have heq : raw2457step0 = raw2457.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2457).symm
    injectiveMoment H raw2457step0 = injectiveMoment H raw2457step1 := by
      have heq : raw2457step1 = (fun i j => raw2457step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2457step0 permutation31 permutation20
    _ = injectiveMoment H node835 := by rfl

def raw2458 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2458step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 0, -1], ![2, -1, 0, -1]]

def raw2458step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2458 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw2458 = injectiveMoment H raw2458step0 := by
      have heq : raw2458step0 = raw2458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2458).symm
    injectiveMoment H raw2458step0 = injectiveMoment H raw2458step1 := by
      have heq : raw2458step1 = (fun i j => raw2458step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2458step0 permutation31 permutation18
    _ = injectiveMoment H node1260 := by rfl

def raw2459 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw2459step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 1, -2], ![2, -1, -1, 0]]

def raw2459step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2459 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw2459 = injectiveMoment H raw2459step0 := by
      have heq : raw2459step0 = raw2459.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2459).symm
    injectiveMoment H raw2459step0 = injectiveMoment H raw2459step1 := by
      have heq : raw2459step1 = (fun i j => raw2459step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2459step0 permutation31 permutation18
    _ = injectiveMoment H node1078 := by rfl

def raw2460 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def raw2460step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 2, -3], ![2, -1, -2, 1]]

def raw2460step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical2460 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2460 = injectiveMoment H node851 := by
  calc
    injectiveMoment H raw2460 = injectiveMoment H raw2460step0 := by
      have heq : raw2460step0 = raw2460.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2460).symm
    injectiveMoment H raw2460step0 = injectiveMoment H raw2460step1 := by
      have heq : raw2460step1 = (fun i j => raw2460step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2460step0 permutation28 permutation18
    _ = injectiveMoment H node851 := by rfl

def raw2461 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 1, -2]]

def raw2461step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical2461 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2461 = injectiveMoment H node846 := by
  calc
    injectiveMoment H raw2461 = injectiveMoment H raw2461step0 := by
      have heq : raw2461step0 = (fun i j => raw2461 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2461 permutation12 permutation15
    _ = injectiveMoment H node846 := by rfl

def raw2462 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2462step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 0, -1, 0], ![2, -1, 0, -1]]

def raw2462step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2462 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw2462 = injectiveMoment H raw2462step0 := by
      have heq : raw2462step0 = raw2462.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2462).symm
    injectiveMoment H raw2462step0 = injectiveMoment H raw2462step1 := by
      have heq : raw2462step1 = (fun i j => raw2462step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2462step0 permutation32 permutation30
    _ = injectiveMoment H node1044 := by rfl

def raw2463 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw2463step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 0, 0, -1], ![2, -1, -1, 0]]

def raw2463step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2463 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw2463 = injectiveMoment H raw2463step0 := by
      have heq : raw2463step0 = raw2463.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2463).symm
    injectiveMoment H raw2463step0 = injectiveMoment H raw2463step1 := by
      have heq : raw2463step1 = (fun i j => raw2463step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2463step0 permutation32 permutation24
    _ = injectiveMoment H node1044 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
