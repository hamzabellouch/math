import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3712 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3712step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw3712step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3712 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3712 = injectiveMoment H node2630 := by
  calc
    injectiveMoment H raw3712 = injectiveMoment H raw3712step0 := by
      have heq : raw3712step0 = -raw3712 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3712).symm
    injectiveMoment H raw3712step0 = injectiveMoment H raw3712step1 := by
      have heq : raw3712step1 = (fun i j => raw3712step0 (permutation149 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3712step0 permutation149 permutation15
    _ = injectiveMoment H node2630 := by rfl

def raw3713 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw3713step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical3713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3713 = injectiveMoment H node2072 := by
  calc
    injectiveMoment H raw3713 = injectiveMoment H raw3713step0 := by
      have heq : raw3713step0 = (fun i j => raw3713 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3713 permutation33 permutation10
    _ = injectiveMoment H node2072 := by rfl

def raw3714 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3714step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw3714step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical3714 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3714 = injectiveMoment H node2581 := by
  calc
    injectiveMoment H raw3714 = injectiveMoment H raw3714step0 := by
      have heq : raw3714step0 = -raw3714 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3714).symm
    injectiveMoment H raw3714step0 = injectiveMoment H raw3714step1 := by
      have heq : raw3714step1 = (fun i j => raw3714step0 (permutation35 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3714step0 permutation35 permutation32
    _ = injectiveMoment H node2581 := by rfl

def raw3715 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3715step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw3715step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical3715 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3715 = injectiveMoment H node2724 := by
  calc
    injectiveMoment H raw3715 = injectiveMoment H raw3715step0 := by
      have heq : raw3715step0 = -raw3715 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3715).symm
    injectiveMoment H raw3715step0 = injectiveMoment H raw3715step1 := by
      have heq : raw3715step1 = (fun i j => raw3715step0 (permutation41 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3715step0 permutation41 permutation30
    _ = injectiveMoment H node2724 := by rfl

def raw3716 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw3716step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 1, 0]]

def raw3716step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical3716 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3716 = injectiveMoment H node2724 := by
  calc
    injectiveMoment H raw3716 = injectiveMoment H raw3716step0 := by
      have heq : raw3716step0 = -raw3716 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3716).symm
    injectiveMoment H raw3716step0 = injectiveMoment H raw3716step1 := by
      have heq : raw3716step1 = (fun i j => raw3716step0 (permutation43 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3716step0 permutation43 permutation30
    _ = injectiveMoment H node2724 := by rfl

def raw3717 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3717step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical3717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3717 = injectiveMoment H node2071 := by
  calc
    injectiveMoment H raw3717 = injectiveMoment H raw3717step0 := by
      have heq : raw3717step0 = (fun i j => raw3717 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3717 permutation33 permutation10
    _ = injectiveMoment H node2071 := by rfl

def raw3718 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3718step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3718step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3718 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3718 = injectiveMoment H node2584 := by
  calc
    injectiveMoment H raw3718 = injectiveMoment H raw3718step0 := by
      have heq : raw3718step0 = -raw3718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3718).symm
    injectiveMoment H raw3718step0 = injectiveMoment H raw3718step1 := by
      have heq : raw3718step1 = (fun i j => raw3718step0 (permutation36 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3718step0 permutation36 permutation32
    _ = injectiveMoment H node2584 := by rfl

def raw3719 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3719step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical3719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3719 = injectiveMoment H node2076 := by
  calc
    injectiveMoment H raw3719 = injectiveMoment H raw3719step0 := by
      have heq : raw3719step0 = (fun i j => raw3719 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3719 permutation33 permutation10
    _ = injectiveMoment H node2076 := by rfl

def raw3720 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3720step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical3720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3720 = injectiveMoment H node2582 := by
  calc
    injectiveMoment H raw3720 = injectiveMoment H raw3720step0 := by
      have heq : raw3720step0 = (fun i j => raw3720 (permutation103 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3720 permutation103 permutation31
    _ = injectiveMoment H node2582 := by rfl

def raw3721 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw3721step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical3721 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3721 = injectiveMoment H node2582 := by
  calc
    injectiveMoment H raw3721 = injectiveMoment H raw3721step0 := by
      have heq : raw3721step0 = (fun i j => raw3721 (permutation97 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3721 permutation97 permutation31
    _ = injectiveMoment H node2582 := by rfl

def raw3722 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3722step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -2, 1, 1], ![-2, 1, 1, 0]]

def raw3722step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3722 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3722 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw3722 = injectiveMoment H raw3722step0 := by
      have heq : raw3722step0 = -raw3722 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3722).symm
    injectiveMoment H raw3722step0 = injectiveMoment H raw3722step1 := by
      have heq : raw3722step1 = (fun i j => raw3722step0 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3722step0 permutation10 permutation32
    _ = injectiveMoment H node1000 := by rfl

def raw3723 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw3723step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -2, 1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw3723step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical3723 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3723 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw3723 = injectiveMoment H raw3723step0 := by
      have heq : raw3723step0 = -raw3723 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3723).symm
    injectiveMoment H raw3723step0 = injectiveMoment H raw3723step1 := by
      have heq : raw3723step1 = (fun i j => raw3723step0 (permutation32 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3723step0 permutation32 permutation13
    _ = injectiveMoment H node510 := by rfl

def raw3724 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3724step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 3, -3], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3724step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical3724 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3724 = injectiveMoment H node920 := by
  calc
    injectiveMoment H raw3724 = injectiveMoment H raw3724step0 := by
      have heq : raw3724step0 = -raw3724 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3724).symm
    injectiveMoment H raw3724step0 = injectiveMoment H raw3724step1 := by
      have heq : raw3724step1 = (fun i j => raw3724step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3724step0 permutation29 permutation15
    _ = injectiveMoment H node920 := by rfl

def raw3725 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3725step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 3, -3], ![-1, 1, -1, 1], ![-1, -1, -1, 3]]

def raw3725step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3725 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3725 = injectiveMoment H node980 := by
  calc
    injectiveMoment H raw3725 = injectiveMoment H raw3725step0 := by
      have heq : raw3725step0 = -raw3725 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3725).symm
    injectiveMoment H raw3725step0 = injectiveMoment H raw3725step1 := by
      have heq : raw3725step1 = (fun i j => raw3725step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3725step0 permutation29 permutation15
    _ = injectiveMoment H node980 := by rfl

def raw3726 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical3726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3726 = injectiveMoment H node2077 := by
  rfl

def raw3727 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

theorem canonical3727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3727 = injectiveMoment H node2078 := by
  rfl

def raw3728 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

theorem canonical3728 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3728 = injectiveMoment H node2079 := by
  rfl

def raw3729 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3729step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![1, -2, -1, 2], ![1, 2, 0, -3]]

def raw3729step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical3729 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3729 = injectiveMoment H node832 := by
  calc
    injectiveMoment H raw3729 = injectiveMoment H raw3729step0 := by
      have heq : raw3729step0 = raw3729.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3729).symm
    injectiveMoment H raw3729step0 = injectiveMoment H raw3729step1 := by
      have heq : raw3729step1 = (fun i j => raw3729step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3729step0 permutation22 permutation23
    _ = injectiveMoment H node832 := by rfl

def raw3730 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3730step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw3730step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

theorem canonical3730 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3730 = injectiveMoment H node1846 := by
  calc
    injectiveMoment H raw3730 = injectiveMoment H raw3730step0 := by
      have heq : raw3730step0 = -raw3730 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3730).symm
    injectiveMoment H raw3730step0 = injectiveMoment H raw3730step1 := by
      have heq : raw3730step1 = (fun i j => raw3730step0 (permutation144 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3730step0 permutation144 permutation11
    _ = injectiveMoment H node1846 := by rfl

def raw3731 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

theorem canonical3731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3731 = injectiveMoment H node2080 := by
  rfl

def raw3732 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3732step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw3732step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3732 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3732 = injectiveMoment H node2761 := by
  calc
    injectiveMoment H raw3732 = injectiveMoment H raw3732step0 := by
      have heq : raw3732step0 = -raw3732 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3732).symm
    injectiveMoment H raw3732step0 = injectiveMoment H raw3732step1 := by
      have heq : raw3732step1 = (fun i j => raw3732step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3732step0 permutation100 permutation15
    _ = injectiveMoment H node2761 := by rfl

def raw3733 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw3733step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-2, 1, -1, 2]]

def raw3733step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3733 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3733 = injectiveMoment H node1281 := by
  calc
    injectiveMoment H raw3733 = injectiveMoment H raw3733step0 := by
      have heq : raw3733step0 = -raw3733 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3733).symm
    injectiveMoment H raw3733step0 = injectiveMoment H raw3733step1 := by
      have heq : raw3733step1 = (fun i j => raw3733step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3733step0 permutation21 permutation17
    _ = injectiveMoment H node1281 := by rfl

def raw3734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw3734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, -1, 2], ![-2, 1, 0, 1]]

def raw3734step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3734 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3734 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw3734 = injectiveMoment H raw3734step0 := by
      have heq : raw3734step0 = -raw3734 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3734).symm
    injectiveMoment H raw3734step0 = injectiveMoment H raw3734step1 := by
      have heq : raw3734step1 = (fun i j => raw3734step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3734step0 permutation21 permutation17
    _ = injectiveMoment H node1010 := by rfl

def raw3735 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3735step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -2, 1, 1], ![-1, 2, -2, 1], ![-1, 0, 0, 1]]

def raw3735step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

theorem canonical3735 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3735 = injectiveMoment H node2066 := by
  calc
    injectiveMoment H raw3735 = injectiveMoment H raw3735step0 := by
      have heq : raw3735step0 = -raw3735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3735).symm
    injectiveMoment H raw3735step0 = injectiveMoment H raw3735step1 := by
      have heq : raw3735step1 = (fun i j => raw3735step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3735step0 permutation100 permutation15
    _ = injectiveMoment H node2066 := by rfl

def raw3736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, -2, 2, -2]]

def raw3736step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -2, -1, 2], ![1, 2, -1, -2]]

def raw3736step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]

theorem canonical3736 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3736 = injectiveMoment H node506 := by
  calc
    injectiveMoment H raw3736 = injectiveMoment H raw3736step0 := by
      have heq : raw3736step0 = raw3736.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3736).symm
    injectiveMoment H raw3736step0 = injectiveMoment H raw3736step1 := by
      have heq : raw3736step1 = (fun i j => raw3736step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3736step0 permutation21 permutation17
    _ = injectiveMoment H node506 := by rfl

def raw3737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -2, 1, -1]]

def raw3737step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-2, 2, -1, 1]]

def raw3737step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

theorem canonical3737 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3737 = injectiveMoment H node523 := by
  calc
    injectiveMoment H raw3737 = injectiveMoment H raw3737step0 := by
      have heq : raw3737step0 = -raw3737 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3737).symm
    injectiveMoment H raw3737step0 = injectiveMoment H raw3737step1 := by
      have heq : raw3737step1 = (fun i j => raw3737step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3737step0 permutation32 permutation11
    _ = injectiveMoment H node523 := by rfl

def raw3738 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 2, 1, -4]]

def raw3738step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![-1, -2, -1, 4]]

def raw3738step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3738 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3738 = injectiveMoment H node450 := by
  calc
    injectiveMoment H raw3738 = injectiveMoment H raw3738step0 := by
      have heq : raw3738step0 = -raw3738 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3738).symm
    injectiveMoment H raw3738step0 = injectiveMoment H raw3738step1 := by
      have heq : raw3738step1 = (fun i j => raw3738step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3738step0 permutation27 permutation17
    _ = injectiveMoment H node450 := by rfl

def raw3739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 2, -1, -2]]

def raw3739step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 2, -2, 1], ![-1, -2, 1, 2]]

def raw3739step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

theorem canonical3739 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3739 = injectiveMoment H node507 := by
  calc
    injectiveMoment H raw3739 = injectiveMoment H raw3739step0 := by
      have heq : raw3739step0 = -raw3739 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3739).symm
    injectiveMoment H raw3739step0 = injectiveMoment H raw3739step1 := by
      have heq : raw3739step1 = (fun i j => raw3739step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3739step0 permutation29 permutation15
    _ = injectiveMoment H node507 := by rfl

def raw3740 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3740step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw3740step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical3740 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3740 = injectiveMoment H node917 := by
  calc
    injectiveMoment H raw3740 = injectiveMoment H raw3740step0 := by
      have heq : raw3740step0 = -raw3740 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3740).symm
    injectiveMoment H raw3740step0 = injectiveMoment H raw3740step1 := by
      have heq : raw3740step1 = (fun i j => raw3740step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3740step0 permutation29 permutation15
    _ = injectiveMoment H node917 := by rfl

def raw3741 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3741step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw3741step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3741 = injectiveMoment H node946 := by
  calc
    injectiveMoment H raw3741 = injectiveMoment H raw3741step0 := by
      have heq : raw3741step0 = -raw3741 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3741).symm
    injectiveMoment H raw3741step0 = injectiveMoment H raw3741step1 := by
      have heq : raw3741step1 = (fun i j => raw3741step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3741step0 permutation27 permutation17
    _ = injectiveMoment H node946 := by rfl

def raw3742 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw3742step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -1, 0, 2]]

def raw3742step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3742 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3742 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw3742 = injectiveMoment H raw3742step0 := by
      have heq : raw3742step0 = -raw3742 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3742).symm
    injectiveMoment H raw3742step0 = injectiveMoment H raw3742step1 := by
      have heq : raw3742step1 = (fun i j => raw3742step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3742step0 permutation29 permutation15
    _ = injectiveMoment H node1058 := by rfl

def raw3743 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw3743step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, -2, 2], ![-1, -1, 1, 1]]

def raw3743step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical3743 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3743 = injectiveMoment H node1111 := by
  calc
    injectiveMoment H raw3743 = injectiveMoment H raw3743step0 := by
      have heq : raw3743step0 = -raw3743 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3743).symm
    injectiveMoment H raw3743step0 = injectiveMoment H raw3743step1 := by
      have heq : raw3743step1 = (fun i j => raw3743step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3743step0 permutation29 permutation16
    _ = injectiveMoment H node1111 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
