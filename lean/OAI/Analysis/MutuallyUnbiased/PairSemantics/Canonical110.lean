import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3520 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw3520step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![0, -3, 3, 0], ![2, 2, -4, 0]]

def raw3520step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem canonical3520 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3520 = injectiveMoment H node1300 := by
  calc
    injectiveMoment H raw3520 = injectiveMoment H raw3520step0 := by
      have heq : raw3520step0 = raw3520.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3520).symm
    injectiveMoment H raw3520step0 = injectiveMoment H raw3520step1 := by
      have heq : raw3520step1 = (fun i j => raw3520step0 (permutation18 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3520step0 permutation18 permutation27
    _ = injectiveMoment H node1300 := by rfl

def raw3521 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical3521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3521 = injectiveMoment H node2039 := by
  rfl

def raw3522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical3522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3522 = injectiveMoment H node2040 := by
  rfl

def raw3523 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical3523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3523 = injectiveMoment H node2041 := by
  rfl

def raw3524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical3524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3524 = injectiveMoment H node2042 := by
  rfl

def raw3525 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw3525step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, -1, 3], ![2, 1, 0, -3]]

def raw3525step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical3525 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3525 = injectiveMoment H node791 := by
  calc
    injectiveMoment H raw3525 = injectiveMoment H raw3525step0 := by
      have heq : raw3525step0 = raw3525.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3525).symm
    injectiveMoment H raw3525step0 = injectiveMoment H raw3525step1 := by
      have heq : raw3525step1 = (fun i j => raw3525step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3525step0 permutation22 permutation23
    _ = injectiveMoment H node791 := by rfl

def raw3526 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3526step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 2, -2, 1], ![-1, 0, 0, 1]]

def raw3526step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3526 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3526 = injectiveMoment H node1840 := by
  calc
    injectiveMoment H raw3526 = injectiveMoment H raw3526step0 := by
      have heq : raw3526step0 = -raw3526 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3526).symm
    injectiveMoment H raw3526step0 = injectiveMoment H raw3526step1 := by
      have heq : raw3526step1 = (fun i j => raw3526step0 (permutation126 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3526step0 permutation126 permutation21
    _ = injectiveMoment H node1840 := by rfl

def raw3527 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

theorem canonical3527 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3527 = injectiveMoment H node2043 := by
  rfl

def raw3528 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3528step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, -2, 2]]

def raw3528step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3528 = injectiveMoment H node1743 := by
  calc
    injectiveMoment H raw3528 = injectiveMoment H raw3528step0 := by
      have heq : raw3528step0 = -raw3528 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3528).symm
    injectiveMoment H raw3528step0 = injectiveMoment H raw3528step1 := by
      have heq : raw3528step1 = (fun i j => raw3528step0 (permutation149 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3528step0 permutation149 permutation21
    _ = injectiveMoment H node1743 := by rfl

def raw3529 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3529step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, 0, 2], ![2, 1, -1, -2]]

def raw3529step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw3529step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3529 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3529 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw3529 = injectiveMoment H raw3529step0 := by
      have heq : raw3529step0 = raw3529.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3529).symm
    injectiveMoment H raw3529step0 = injectiveMoment H raw3529step1 := by
      have heq : raw3529step1 = -raw3529step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3529step0).symm
    injectiveMoment H raw3529step1 = injectiveMoment H raw3529step2 := by
      have heq : raw3529step2 = (fun i j => raw3529step1 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3529step1 permutation15 permutation23
    _ = injectiveMoment H node1059 := by rfl

def raw3530 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical3530 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3530 = injectiveMoment H node2044 := by
  rfl

def raw3531 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3531step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, -1, 2], ![-2, 2, -1, 1]]

def raw3531step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical3531 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3531 = injectiveMoment H node520 := by
  calc
    injectiveMoment H raw3531 = injectiveMoment H raw3531step0 := by
      have heq : raw3531step0 = -raw3531 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3531).symm
    injectiveMoment H raw3531step0 = injectiveMoment H raw3531step1 := by
      have heq : raw3531step1 = (fun i j => raw3531step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3531step0 permutation32 permutation11
    _ = injectiveMoment H node520 := by rfl

def raw3532 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3532step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3532step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical3532 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3532 = injectiveMoment H node1695 := by
  calc
    injectiveMoment H raw3532 = injectiveMoment H raw3532step0 := by
      have heq : raw3532step0 = -raw3532 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3532).symm
    injectiveMoment H raw3532step0 = injectiveMoment H raw3532step1 := by
      have heq : raw3532step1 = (fun i j => raw3532step0 (permutation83 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3532step0 permutation83 permutation23
    _ = injectiveMoment H node1695 := by rfl

def raw3533 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3533step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, 2, 0], ![2, 1, -3, 0]]

def raw3533step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![-2, -1, 3, 0]]

def raw3533step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical3533 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3533 = injectiveMoment H node474 := by
  calc
    injectiveMoment H raw3533 = injectiveMoment H raw3533step0 := by
      have heq : raw3533step0 = raw3533.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3533).symm
    injectiveMoment H raw3533step0 = injectiveMoment H raw3533step1 := by
      have heq : raw3533step1 = -raw3533step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3533step0).symm
    injectiveMoment H raw3533step1 = injectiveMoment H raw3533step2 := by
      have heq : raw3533step2 = (fun i j => raw3533step1 (permutation30 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3533step1 permutation30 permutation10
    _ = injectiveMoment H node474 := by rfl

def raw3534 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem canonical3534 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3534 = injectiveMoment H node2045 := by
  rfl

def raw3535 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical3535 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3535 = injectiveMoment H node2046 := by
  rfl

def raw3536 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3536step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical3536 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3536 = injectiveMoment H node2046 := by
  calc
    injectiveMoment H raw3536 = injectiveMoment H raw3536step0 := by
      have heq : raw3536step0 = (fun i j => raw3536 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3536 permutation34 permutation9
    _ = injectiveMoment H node2046 := by rfl

def raw3537 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw3537step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, 3, -1], ![2, 1, -4, 1]]

def raw3537step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, -3, 1], ![-2, -1, 4, -1]]

def raw3537step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, 0, -2, 0]]

theorem canonical3537 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3537 = injectiveMoment H node451 := by
  calc
    injectiveMoment H raw3537 = injectiveMoment H raw3537step0 := by
      have heq : raw3537step0 = raw3537.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3537).symm
    injectiveMoment H raw3537step0 = injectiveMoment H raw3537step1 := by
      have heq : raw3537step1 = -raw3537step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3537step0).symm
    injectiveMoment H raw3537step1 = injectiveMoment H raw3537step2 := by
      have heq : raw3537step2 = (fun i j => raw3537step1 (permutation30 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3537step1 permutation30 permutation10
    _ = injectiveMoment H node451 := by rfl

def raw3538 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3538step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw3538step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3538 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3538 = injectiveMoment H node450 := by
  calc
    injectiveMoment H raw3538 = injectiveMoment H raw3538step0 := by
      have heq : raw3538step0 = -raw3538 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3538).symm
    injectiveMoment H raw3538step0 = injectiveMoment H raw3538step1 := by
      have heq : raw3538step1 = (fun i j => raw3538step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3538step0 permutation31 permutation21
    _ = injectiveMoment H node450 := by rfl

def raw3539 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3539step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw3539step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw3539step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3539 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3539 = injectiveMoment H node473 := by
  calc
    injectiveMoment H raw3539 = injectiveMoment H raw3539step0 := by
      have heq : raw3539step0 = raw3539.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3539).symm
    injectiveMoment H raw3539step0 = injectiveMoment H raw3539step1 := by
      have heq : raw3539step1 = -raw3539step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3539step0).symm
    injectiveMoment H raw3539step1 = injectiveMoment H raw3539step2 := by
      have heq : raw3539step2 = (fun i j => raw3539step1 (permutation30 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3539step1 permutation30 permutation9
    _ = injectiveMoment H node473 := by rfl

def raw3540 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 2, -2, 1], ![-1, -1, 0, 2]]

def raw3540step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3540 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3540 = injectiveMoment H node521 := by
  calc
    injectiveMoment H raw3540 = injectiveMoment H raw3540step0 := by
      have heq : raw3540step0 = -raw3540 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3540).symm
    injectiveMoment H raw3540step0 = injectiveMoment H raw3540step1 := by
      have heq : raw3540step1 = (fun i j => raw3540step0 (permutation25 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3540step0 permutation25 permutation21
    _ = injectiveMoment H node521 := by rfl

def raw3541 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -2, 3, -1], ![2, 1, -2, -1]]

def raw3541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

theorem canonical3541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3541 = injectiveMoment H node488 := by
  calc
    injectiveMoment H raw3541 = injectiveMoment H raw3541step0 := by
      have heq : raw3541step0 = raw3541.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3541).symm
    injectiveMoment H raw3541step0 = injectiveMoment H raw3541step1 := by
      have heq : raw3541step1 = (fun i j => raw3541step0 (permutation22 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3541step0 permutation22 permutation19
    _ = injectiveMoment H node488 := by rfl

def raw3542 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3542step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 1, 1, -1], ![-1, 0, -3, 4]]

def raw3542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3542 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3542 = injectiveMoment H node1306 := by
  calc
    injectiveMoment H raw3542 = injectiveMoment H raw3542step0 := by
      have heq : raw3542step0 = -raw3542 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3542).symm
    injectiveMoment H raw3542step0 = injectiveMoment H raw3542step1 := by
      have heq : raw3542step1 = (fun i j => raw3542step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3542step0 permutation19 permutation15
    _ = injectiveMoment H node1306 := by rfl

def raw3543 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3543step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical3543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3543 = injectiveMoment H node1301 := by
  calc
    injectiveMoment H raw3543 = injectiveMoment H raw3543step0 := by
      have heq : raw3543step0 = (fun i j => raw3543 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3543 permutation22 permutation17
    _ = injectiveMoment H node1301 := by rfl

def raw3544 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3544step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw3544step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3544 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3544 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw3544 = injectiveMoment H raw3544step0 := by
      have heq : raw3544step0 = -raw3544 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3544).symm
    injectiveMoment H raw3544step0 = injectiveMoment H raw3544step1 := by
      have heq : raw3544step1 = (fun i j => raw3544step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3544step0 permutation19 permutation15
    _ = injectiveMoment H node1309 := by rfl

def raw3545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw3545step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3545 = injectiveMoment H node1311 := by
  calc
    injectiveMoment H raw3545 = injectiveMoment H raw3545step0 := by
      have heq : raw3545step0 = -raw3545 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3545).symm
    injectiveMoment H raw3545step0 = injectiveMoment H raw3545step1 := by
      have heq : raw3545step1 = (fun i j => raw3545step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3545step0 permutation19 permutation15
    _ = injectiveMoment H node1311 := by rfl

def raw3546 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3546step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -2, 3, -1], ![2, 1, -3, 0]]

def raw3546step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical3546 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3546 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw3546 = injectiveMoment H raw3546step0 := by
      have heq : raw3546step0 = raw3546.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3546).symm
    injectiveMoment H raw3546step0 = injectiveMoment H raw3546step1 := by
      have heq : raw3546step1 = (fun i j => raw3546step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3546step0 permutation24 permutation29
    _ = injectiveMoment H node819 := by rfl

def raw3547 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw3547step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![2, 1, 0, -3]]

def raw3547step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical3547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3547 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw3547 = injectiveMoment H raw3547step0 := by
      have heq : raw3547step0 = raw3547.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3547).symm
    injectiveMoment H raw3547step0 = injectiveMoment H raw3547step1 := by
      have heq : raw3547step1 = (fun i j => raw3547step0 (permutation24 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3547step0 permutation24 permutation23
    _ = injectiveMoment H node819 := by rfl

def raw3548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 0, 3, -4], ![1, -1, -1, 1]]

def raw3548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 0, -3, 4], ![-1, 1, 1, -1]]

def raw3548step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3548 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3548 = injectiveMoment H node1306 := by
  calc
    injectiveMoment H raw3548 = injectiveMoment H raw3548step0 := by
      have heq : raw3548step0 = -raw3548 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3548).symm
    injectiveMoment H raw3548step0 = injectiveMoment H raw3548step1 := by
      have heq : raw3548step1 = (fun i j => raw3548step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3548step0 permutation17 permutation15
    _ = injectiveMoment H node1306 := by rfl

def raw3549 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 1, 0, -2], ![1, -2, 2, -1]]

def raw3549step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, -1, 0, 2], ![-1, 2, -2, 1]]

def raw3549step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3549 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3549 = injectiveMoment H node521 := by
  calc
    injectiveMoment H raw3549 = injectiveMoment H raw3549step0 := by
      have heq : raw3549step0 = -raw3549 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3549).symm
    injectiveMoment H raw3549step0 = injectiveMoment H raw3549step1 := by
      have heq : raw3549step1 = (fun i j => raw3549step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3549step0 permutation31 permutation21
    _ = injectiveMoment H node521 := by rfl

def raw3550 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 1, 2, -4], ![1, -2, 0, 1]]

def raw3550step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, -1, -2, 4], ![-1, 2, 0, -1]]

def raw3550step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3550 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3550 = injectiveMoment H node450 := by
  calc
    injectiveMoment H raw3550 = injectiveMoment H raw3550step0 := by
      have heq : raw3550step0 = -raw3550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3550).symm
    injectiveMoment H raw3550step0 = injectiveMoment H raw3550step1 := by
      have heq : raw3550step1 = (fun i j => raw3550step0 (permutation25 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3550step0 permutation25 permutation21
    _ = injectiveMoment H node450 := by rfl

def raw3551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3551step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, -3, 4]]

def raw3551step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3551 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3551 = injectiveMoment H node2807 := by
  calc
    injectiveMoment H raw3551 = injectiveMoment H raw3551step0 := by
      have heq : raw3551step0 = -raw3551 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3551).symm
    injectiveMoment H raw3551step0 = injectiveMoment H raw3551step1 := by
      have heq : raw3551step1 = (fun i j => raw3551step0 (permutation76 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3551step0 permutation76 permutation15
    _ = injectiveMoment H node2807 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
