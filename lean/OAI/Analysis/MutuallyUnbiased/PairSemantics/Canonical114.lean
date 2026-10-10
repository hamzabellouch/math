import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3648 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -2, 1, 2], ![3, 2, -2, -3]]

def raw3648step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical3648 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3648 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw3648 = injectiveMoment H raw3648step0 := by
      have heq : raw3648step0 = raw3648.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3648).symm
    _ = injectiveMoment H node167 := by rfl

def raw3649 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -2, 2, 1], ![3, 2, -3, -2]]

def raw3649step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]

def raw3649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical3649 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3649 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw3649 = injectiveMoment H raw3649step0 := by
      have heq : raw3649step0 = raw3649.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3649).symm
    injectiveMoment H raw3649step0 = injectiveMoment H raw3649step1 := by
      have heq : raw3649step1 = (fun i j => raw3649step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3649step0 permutation10 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw3650 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -2, 3, 0], ![3, 2, -4, -1]]

def raw3650step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]

def raw3650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

theorem canonical3650 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3650 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw3650 = injectiveMoment H raw3650step0 := by
      have heq : raw3650step0 = raw3650.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3650).symm
    injectiveMoment H raw3650step0 = injectiveMoment H raw3650step1 := by
      have heq : raw3650step1 = (fun i j => raw3650step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3650step0 permutation10 permutation3
    _ = injectiveMoment H node166 := by rfl

def raw3651 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -2, 1], ![3, -2, 1, -2]]

def raw3651step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3651 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw3651 = injectiveMoment H raw3651step0 := by
      have heq : raw3651step0 = raw3651.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3651).symm
    _ = injectiveMoment H node184 := by rfl

def raw3652 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 1, -2], ![3, -2, -2, 1]]

def raw3652step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]

def raw3652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3652 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw3652 = injectiveMoment H raw3652step0 := by
      have heq : raw3652step0 = raw3652.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3652).symm
    injectiveMoment H raw3652step0 = injectiveMoment H raw3652step1 := by
      have heq : raw3652step1 = (fun i j => raw3652step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3652step0 permutation10 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw3653 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 3, -2, 0], ![3, -3, 1, -1]]

def raw3653step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical3653 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3653 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw3653 = injectiveMoment H raw3653step0 := by
      have heq : raw3653step0 = raw3653.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3653).symm
    _ = injectiveMoment H node187 := by rfl

def raw3654 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 4, -2, -1], ![3, -4, 1, 0]]

def raw3654step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical3654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3654 = injectiveMoment H node190 := by
  calc
    injectiveMoment H raw3654 = injectiveMoment H raw3654step0 := by
      have heq : raw3654step0 = raw3654.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3654).symm
    _ = injectiveMoment H node190 := by rfl

def raw3655 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -3, 1, 2], ![2, 3, -2, -3]]

def raw3655step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical3655 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3655 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw3655 = injectiveMoment H raw3655step0 := by
      have heq : raw3655step0 = raw3655.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3655).symm
    _ = injectiveMoment H node196 := by rfl

def raw3656 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, -2, 4], ![2, 2, 1, -5]]

def raw3656step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

theorem canonical3656 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3656 = injectiveMoment H node200 := by
  calc
    injectiveMoment H raw3656 = injectiveMoment H raw3656step0 := by
      have heq : raw3656step0 = raw3656.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3656).symm
    _ = injectiveMoment H node200 := by rfl

def raw3657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3657step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical3657 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3657 = injectiveMoment H node1940 := by
  calc
    injectiveMoment H raw3657 = injectiveMoment H raw3657step0 := by
      have heq : raw3657step0 = (fun i j => raw3657 (permutation59 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3657 permutation59 permutation15
    _ = injectiveMoment H node1940 := by rfl

def raw3658 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, -1, 3], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3658step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical3658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3658 = injectiveMoment H node487 := by
  calc
    injectiveMoment H raw3658 = injectiveMoment H raw3658step0 := by
      have heq : raw3658step0 = (fun i j => raw3658 (permutation15 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3658 permutation15 permutation17
    _ = injectiveMoment H node487 := by rfl

def raw3659 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3659step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical3659 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3659 = injectiveMoment H node1990 := by
  calc
    injectiveMoment H raw3659 = injectiveMoment H raw3659step0 := by
      have heq : raw3659step0 = (fun i j => raw3659 (permutation57 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3659 permutation57 permutation15
    _ = injectiveMoment H node1990 := by rfl

def raw3660 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3660step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical3660 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3660 = injectiveMoment H node1993 := by
  calc
    injectiveMoment H raw3660 = injectiveMoment H raw3660step0 := by
      have heq : raw3660step0 = (fun i j => raw3660 (permutation59 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3660 permutation59 permutation15
    _ = injectiveMoment H node1993 := by rfl

def raw3661 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw3661step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw3661step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw3661step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3661 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3661 = injectiveMoment H node473 := by
  calc
    injectiveMoment H raw3661 = injectiveMoment H raw3661step0 := by
      have heq : raw3661step0 = raw3661.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3661).symm
    injectiveMoment H raw3661step0 = injectiveMoment H raw3661step1 := by
      have heq : raw3661step1 = -raw3661step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3661step0).symm
    injectiveMoment H raw3661step1 = injectiveMoment H raw3661step2 := by
      have heq : raw3661step2 = (fun i j => raw3661step1 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3661step1 permutation31 permutation15
    _ = injectiveMoment H node473 := by rfl

def raw3662 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical3662 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3662 = injectiveMoment H node2056 := by
  rfl

def raw3663 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical3663 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3663 = injectiveMoment H node2057 := by
  rfl

def raw3664 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw3664step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical3664 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3664 = injectiveMoment H node2057 := by
  calc
    injectiveMoment H raw3664 = injectiveMoment H raw3664step0 := by
      have heq : raw3664step0 = (fun i j => raw3664 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3664 permutation34 permutation9
    _ = injectiveMoment H node2057 := by rfl

def raw3665 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3665step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical3665 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3665 = injectiveMoment H node2056 := by
  calc
    injectiveMoment H raw3665 = injectiveMoment H raw3665step0 := by
      have heq : raw3665step0 = (fun i j => raw3665 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3665 permutation33 permutation10
    _ = injectiveMoment H node2056 := by rfl

def raw3666 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3666step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw3666step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def raw3666step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3666 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3666 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw3666 = injectiveMoment H raw3666step0 := by
      have heq : raw3666step0 = raw3666.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3666).symm
    injectiveMoment H raw3666step0 = injectiveMoment H raw3666step1 := by
      have heq : raw3666step1 = -raw3666step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3666step0).symm
    injectiveMoment H raw3666step1 = injectiveMoment H raw3666step2 := by
      have heq : raw3666step2 = (fun i j => raw3666step1 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3666step1 permutation17 permutation21
    _ = injectiveMoment H node1309 := by rfl

def raw3667 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3667step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -2, 2, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3667step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3667 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3667 = injectiveMoment H node2013 := by
  calc
    injectiveMoment H raw3667 = injectiveMoment H raw3667step0 := by
      have heq : raw3667step0 = -raw3667 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3667).symm
    injectiveMoment H raw3667step0 = injectiveMoment H raw3667step1 := by
      have heq : raw3667step1 = (fun i j => raw3667step0 (permutation96 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3667step0 permutation96 permutation16
    _ = injectiveMoment H node2013 := by rfl

def raw3668 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3668step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical3668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3668 = injectiveMoment H node2055 := by
  calc
    injectiveMoment H raw3668 = injectiveMoment H raw3668step0 := by
      have heq : raw3668step0 = (fun i j => raw3668 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3668 permutation60 permutation15
    _ = injectiveMoment H node2055 := by rfl

def raw3669 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3669step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical3669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3669 = injectiveMoment H node608 := by
  calc
    injectiveMoment H raw3669 = injectiveMoment H raw3669step0 := by
      have heq : raw3669step0 = raw3669.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3669).symm
    _ = injectiveMoment H node608 := by rfl

def raw3670 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw3670step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3670step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def raw3670step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3670 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3670 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw3670 = injectiveMoment H raw3670step0 := by
      have heq : raw3670step0 = raw3670.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3670).symm
    injectiveMoment H raw3670step0 = injectiveMoment H raw3670step1 := by
      have heq : raw3670step1 = -raw3670step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3670step0).symm
    injectiveMoment H raw3670step1 = injectiveMoment H raw3670step2 := by
      have heq : raw3670step2 = (fun i j => raw3670step1 (permutation13 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3670step1 permutation13 permutation23
    _ = injectiveMoment H node1309 := by rfl

def raw3671 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3671step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw3671step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def raw3671step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3671 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw3671 = injectiveMoment H raw3671step0 := by
      have heq : raw3671step0 = raw3671.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3671).symm
    injectiveMoment H raw3671step0 = injectiveMoment H raw3671step1 := by
      have heq : raw3671step1 = -raw3671step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3671step0).symm
    injectiveMoment H raw3671step1 = injectiveMoment H raw3671step2 := by
      have heq : raw3671step2 = (fun i j => raw3671step1 (permutation11 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3671step1 permutation11 permutation23
    _ = injectiveMoment H node1309 := by rfl

def raw3672 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical3672 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3672 = injectiveMoment H node613 := by
  rfl

def raw3673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical3673 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3673 = injectiveMoment H node614 := by
  rfl

def raw3674 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![2, 2, -2, -2]]

def raw3674step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical3674 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3674 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw3674 = injectiveMoment H raw3674step0 := by
      have heq : raw3674step0 = raw3674.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3674).symm
    _ = injectiveMoment H node202 := by rfl

def raw3675 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 2, 0], ![2, 2, -3, -1]]

def raw3675step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]

def raw3675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw3675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical3675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3675 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw3675 = injectiveMoment H raw3675step0 := by
      have heq : raw3675step0 = raw3675.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3675).symm
    injectiveMoment H raw3675step0 = injectiveMoment H raw3675step1 := by
      have heq : raw3675step1 = -raw3675step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3675step0).symm
    injectiveMoment H raw3675step1 = injectiveMoment H raw3675step2 := by
      have heq : raw3675step2 = (fun i j => raw3675step1 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3675step1 permutation25 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw3676 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 3, -1], ![2, 2, -4, 0]]

def raw3676step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]

def raw3676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical3676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3676 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw3676 = injectiveMoment H raw3676step0 := by
      have heq : raw3676step0 = raw3676.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3676).symm
    injectiveMoment H raw3676step0 = injectiveMoment H raw3676step1 := by
      have heq : raw3676step1 = (fun i j => raw3676step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3676step0 permutation10 permutation3
    _ = injectiveMoment H node201 := by rfl

def raw3677 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical3677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3677 = injectiveMoment H node2058 := by
  rfl

def raw3678 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 2, 1, -4]]

def raw3678step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -2, 0, 1], ![1, 3, 0, -4]]

def raw3678step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical3678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3678 = injectiveMoment H node1278 := by
  calc
    injectiveMoment H raw3678 = injectiveMoment H raw3678step0 := by
      have heq : raw3678step0 = raw3678.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3678).symm
    injectiveMoment H raw3678step0 = injectiveMoment H raw3678step1 := by
      have heq : raw3678step1 = (fun i j => raw3678step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3678step0 permutation18 permutation21
    _ = injectiveMoment H node1278 := by rfl

def raw3679 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3679step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 2, -3], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3679step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical3679 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3679 = injectiveMoment H node892 := by
  calc
    injectiveMoment H raw3679 = injectiveMoment H raw3679step0 := by
      have heq : raw3679step0 = -raw3679 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3679).symm
    injectiveMoment H raw3679step0 = injectiveMoment H raw3679step1 := by
      have heq : raw3679step1 = (fun i j => raw3679step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3679step0 permutation31 permutation15
    _ = injectiveMoment H node892 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
