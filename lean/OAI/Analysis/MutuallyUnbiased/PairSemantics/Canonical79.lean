import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2528 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, 2, -2, 1], ![3, -1, 0, -2]]

def raw2528step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, 1, -2]]

def raw2528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-2, 2, 0], ![-1, -1, 2]]

def raw2528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2528 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2528 = injectiveMoment H raw2528step0 := by
      have heq : raw2528step0 = raw2528.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2528).symm
    injectiveMoment H raw2528step0 = injectiveMoment H raw2528step1 := by
      have heq : raw2528step1 = -raw2528step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2528step0).symm
    injectiveMoment H raw2528step1 = injectiveMoment H raw2528step2 := by
      have heq : raw2528step2 = (fun i j => raw2528step1 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2528step1 permutation11 permutation8
    _ = injectiveMoment H node111 := by rfl

def raw2529 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, 2, 1, -2], ![3, -1, -3, 1]]

def raw2529step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, 1, -3], ![1, -2, 1]]

def raw2529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical2529 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2529 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw2529 = injectiveMoment H raw2529step0 := by
      have heq : raw2529step0 = raw2529.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2529).symm
    injectiveMoment H raw2529step0 = injectiveMoment H raw2529step1 := by
      have heq : raw2529step1 = (fun i j => raw2529step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2529step0 permutation10 permutation3
    _ = injectiveMoment H node159 := by rfl

def raw2530 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, 3, 0, -2], ![3, -2, -2, 1]]

def raw2530step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![2, 0, -2], ![1, -2, 1]]

def raw2530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-2, 0, 2], ![-1, 2, -1]]

def raw2530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical2530 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2530 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw2530 = injectiveMoment H raw2530step0 := by
      have heq : raw2530step0 = raw2530.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2530).symm
    injectiveMoment H raw2530step0 = injectiveMoment H raw2530step1 := by
      have heq : raw2530step1 = -raw2530step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2530step0).symm
    injectiveMoment H raw2530step1 = injectiveMoment H raw2530step2 := by
      have heq : raw2530step2 = (fun i j => raw2530step1 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2530step1 permutation17 permutation5
    _ = injectiveMoment H node103 := by rfl

def raw2531 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, 4, -1, -2], ![3, -3, -1, 1]]

def raw2531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![2, -1, -1], ![1, -2, 1]]

def raw2531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2531 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2531 = injectiveMoment H node161 := by
  calc
    injectiveMoment H raw2531 = injectiveMoment H raw2531step0 := by
      have heq : raw2531step0 = raw2531.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2531).symm
    injectiveMoment H raw2531step0 = injectiveMoment H raw2531step1 := by
      have heq : raw2531step1 = (fun i j => raw2531step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2531step0 permutation10 permutation3
    _ = injectiveMoment H node161 := by rfl

def raw2532 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -2, 1, 1], ![2, 3, -3, -2]]

def raw2532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![2, 1, -3], ![1, 1, -2]]

def raw2532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2532 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2532 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw2532 = injectiveMoment H raw2532step0 := by
      have heq : raw2532step0 = raw2532.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2532).symm
    injectiveMoment H raw2532step0 = injectiveMoment H raw2532step1 := by
      have heq : raw2532step1 = (fun i j => raw2532step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2532step0 permutation16 permutation5
    _ = injectiveMoment H node167 := by rfl

def raw2533 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2533step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -2, 1]]

theorem canonical2533 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2533 = injectiveMoment H node482 := by
  calc
    injectiveMoment H raw2533 = injectiveMoment H raw2533step0 := by
      have heq : raw2533step0 = (fun i j => raw2533 (permutation20 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2533 permutation20 permutation23
    _ = injectiveMoment H node482 := by rfl

def raw2534 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -2, 3], ![2, 2, 0, -4]]

def raw2534step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![2, -2, 0], ![1, 3, -4]]

def raw2534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, 2, 0], ![-1, -3, 4]]

def raw2534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical2534 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2534 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw2534 = injectiveMoment H raw2534step0 := by
      have heq : raw2534step0 = raw2534.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2534).symm
    injectiveMoment H raw2534step0 = injectiveMoment H raw2534step1 := by
      have heq : raw2534step1 = -raw2534step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2534step0).symm
    injectiveMoment H raw2534step1 = injectiveMoment H raw2534step2 := by
      have heq : raw2534step2 = (fun i j => raw2534step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2534step1 permutation27 permutation5
    _ = injectiveMoment H node85 := by rfl

def raw2535 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem canonical2535 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2535 = injectiveMoment H node1832 := by
  rfl

def raw2536 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical2536 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2536 = injectiveMoment H node1833 := by
  rfl

def raw2537 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical2537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2537 = injectiveMoment H node1834 := by
  rfl

def raw2538 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical2538 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2538 = injectiveMoment H node1835 := by
  rfl

def raw2539 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical2539 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2539 = injectiveMoment H node1836 := by
  rfl

def raw2540 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw2540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![2, -1, 0, -1], ![1, 2, -1, -2]]

def raw2540step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, 1, -1, -1], ![-2, 1, 0, 1], ![-1, -2, 1, 2]]

def raw2540step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical2540 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2540 = injectiveMoment H node1346 := by
  calc
    injectiveMoment H raw2540 = injectiveMoment H raw2540step0 := by
      have heq : raw2540step0 = raw2540.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2540).symm
    injectiveMoment H raw2540step0 = injectiveMoment H raw2540step1 := by
      have heq : raw2540step1 = -raw2540step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2540step0).symm
    injectiveMoment H raw2540step1 = injectiveMoment H raw2540step2 := by
      have heq : raw2540step2 = (fun i j => raw2540step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2540step1 permutation15 permutation24
    _ = injectiveMoment H node1346 := by rfl

def raw2541 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical2541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2541 = injectiveMoment H node1837 := by
  rfl

def raw2542 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical2542 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2542 = injectiveMoment H node520 := by
  rfl

def raw2543 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical2543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2543 = injectiveMoment H node1838 := by
  rfl

def raw2544 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical2544 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2544 = injectiveMoment H node521 := by
  rfl

def raw2545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw2545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![2, -1, -1, 0], ![1, 2, 0, -3]]

def raw2545step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical2545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2545 = injectiveMoment H node1007 := by
  calc
    injectiveMoment H raw2545 = injectiveMoment H raw2545step0 := by
      have heq : raw2545step0 = raw2545.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2545).symm
    injectiveMoment H raw2545step0 = injectiveMoment H raw2545step1 := by
      have heq : raw2545step1 = (fun i j => raw2545step0 (permutation24 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2545step0 permutation24 permutation24
    _ = injectiveMoment H node1007 := by rfl

def raw2546 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw2546step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![2, -1, 0, -1], ![1, 2, -1, -2]]

def raw2546step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, 0, -2], ![-2, 1, 0, 1], ![-1, -2, 1, 2]]

def raw2546step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical2546 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2546 = injectiveMoment H node1276 := by
  calc
    injectiveMoment H raw2546 = injectiveMoment H raw2546step0 := by
      have heq : raw2546step0 = raw2546.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2546).symm
    injectiveMoment H raw2546step0 = injectiveMoment H raw2546step1 := by
      have heq : raw2546step1 = -raw2546step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2546step0).symm
    injectiveMoment H raw2546step1 = injectiveMoment H raw2546step2 := by
      have heq : raw2546step2 = (fun i j => raw2546step1 (permutation9 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2546step1 permutation9 permutation24
    _ = injectiveMoment H node1276 := by rfl

def raw2547 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical2547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2547 = injectiveMoment H node522 := by
  rfl

def raw2548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 2, -1, -2], ![1, 0, 0, -1]]

def raw2548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![2, -1, -1, 0], ![1, 2, -2, -1]]

def raw2548step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, -2, 0], ![-2, 1, 1, 0], ![-1, -2, 2, 1]]

def raw2548step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical2548 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2548 = injectiveMoment H node1276 := by
  calc
    injectiveMoment H raw2548 = injectiveMoment H raw2548step0 := by
      have heq : raw2548step0 = raw2548.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2548).symm
    injectiveMoment H raw2548step0 = injectiveMoment H raw2548step1 := by
      have heq : raw2548step1 = -raw2548step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2548step0).symm
    injectiveMoment H raw2548step1 = injectiveMoment H raw2548step2 := by
      have heq : raw2548step2 = (fun i j => raw2548step1 (permutation9 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2548step1 permutation9 permutation30
    _ = injectiveMoment H node1276 := by rfl

def raw2549 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 2, -1], ![2, 2, -4, 0]]

def raw2549step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![2, 2, -4], ![1, -1, 0]]

def raw2549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, -2, 4], ![-1, 1, 0]]

def raw2549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2549 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2549 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw2549 = injectiveMoment H raw2549step0 := by
      have heq : raw2549step0 = raw2549.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2549).symm
    injectiveMoment H raw2549step0 = injectiveMoment H raw2549step1 := by
      have heq : raw2549step1 = -raw2549step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2549step0).symm
    injectiveMoment H raw2549step1 = injectiveMoment H raw2549step2 := by
      have heq : raw2549step2 = (fun i j => raw2549step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2549step1 permutation22 permutation5
    _ = injectiveMoment H node153 := by rfl

def raw2550 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 3, -2], ![2, 2, -5, 1]]

def raw2550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![2, 3, -5], ![1, -2, 1]]

def raw2550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, -3, 5], ![-1, 2, -1]]

def raw2550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical2550 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2550 = injectiveMoment H node74 := by
  calc
    injectiveMoment H raw2550 = injectiveMoment H raw2550step0 := by
      have heq : raw2550step0 = raw2550.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2550).symm
    injectiveMoment H raw2550step0 = injectiveMoment H raw2550step1 := by
      have heq : raw2550step1 = -raw2550step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2550step0).symm
    injectiveMoment H raw2550step1 = injectiveMoment H raw2550step2 := by
      have heq : raw2550step2 = (fun i j => raw2550step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2550step1 permutation21 permutation5
    _ = injectiveMoment H node74 := by rfl

def raw2551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2551step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem canonical2551 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2551 = injectiveMoment H node1813 := by
  calc
    injectiveMoment H raw2551 = injectiveMoment H raw2551step0 := by
      have heq : raw2551step0 = (fun i j => raw2551 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2551 permutation33 permutation10
    _ = injectiveMoment H node1813 := by rfl

def raw2552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical2552 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2552 = injectiveMoment H node1843 := by
  rfl

def raw2553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical2553 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2553 = injectiveMoment H node1844 := by
  rfl

def raw2554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2554step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical2554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2554 = injectiveMoment H node2453 := by
  calc
    injectiveMoment H raw2554 = injectiveMoment H raw2554step0 := by
      have heq : raw2554step0 = (fun i j => raw2554 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2554 permutation36 permutation15
    _ = injectiveMoment H node2453 := by rfl

def raw2555 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2555step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical2555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2555 = injectiveMoment H node854 := by
  calc
    injectiveMoment H raw2555 = injectiveMoment H raw2555step0 := by
      have heq : raw2555step0 = (fun i j => raw2555 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2555 permutation10 permutation15
    _ = injectiveMoment H node854 := by rfl

def raw2556 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2556step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2556 = injectiveMoment H node844 := by
  calc
    injectiveMoment H raw2556 = injectiveMoment H raw2556step0 := by
      have heq : raw2556step0 = (fun i j => raw2556 (permutation10 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2556 permutation10 permutation16
    _ = injectiveMoment H node844 := by rfl

def raw2557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2557 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2557 = injectiveMoment H node1845 := by
  rfl

def raw2558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

theorem canonical2558 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2558 = injectiveMoment H node523 := by
  rfl

def raw2559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2559step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2559 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2559 = injectiveMoment H node1814 := by
  calc
    injectiveMoment H raw2559 = injectiveMoment H raw2559step0 := by
      have heq : raw2559step0 = (fun i j => raw2559 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2559 permutation33 permutation10
    _ = injectiveMoment H node1814 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
