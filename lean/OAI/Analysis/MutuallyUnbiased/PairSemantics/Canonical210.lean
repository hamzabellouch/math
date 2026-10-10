import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6720 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw6720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6720 = injectiveMoment H node860 := by
  calc
    injectiveMoment H raw6720 = injectiveMoment H raw6720step0 := by
      have heq : raw6720step0 = (fun i j => raw6720 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6720 permutation57 permutation3
    _ = injectiveMoment H node860 := by rfl

def raw6721 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw6721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6721 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6721 = injectiveMoment H node861 := by
  calc
    injectiveMoment H raw6721 = injectiveMoment H raw6721step0 := by
      have heq : raw6721step0 = (fun i j => raw6721 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6721 permutation57 permutation3
    _ = injectiveMoment H node861 := by rfl

def raw6722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw6722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw6722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6722 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6722 = injectiveMoment H node866 := by
  calc
    injectiveMoment H raw6722 = injectiveMoment H raw6722step0 := by
      have heq : raw6722step0 = -raw6722 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6722).symm
    injectiveMoment H raw6722step0 = injectiveMoment H raw6722step1 := by
      have heq : raw6722step1 = (fun i j => raw6722step0 (permutation149 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6722step0 permutation149 permutation3
    _ = injectiveMoment H node866 := by rfl

def raw6723 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6723 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6723 = injectiveMoment H node1130 := by
  rfl

def raw6724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw6724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6724 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6724 = injectiveMoment H node1130 := by
  calc
    injectiveMoment H raw6724 = injectiveMoment H raw6724step0 := by
      have heq : raw6724step0 = (fun i j => raw6724 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6724 permutation34 permutation3
    _ = injectiveMoment H node1130 := by rfl

def raw6725 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6725 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6725 = injectiveMoment H node1131 := by
  rfl

def raw6726 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw6726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]

def raw6726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6726 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6726 = injectiveMoment H node654 := by
  calc
    injectiveMoment H raw6726 = injectiveMoment H raw6726step0 := by
      have heq : raw6726step0 = -raw6726 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6726).symm
    injectiveMoment H raw6726step0 = injectiveMoment H raw6726step1 := by
      have heq : raw6726step1 = (fun i j => raw6726step0 (permutation96 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6726step0 permutation96 permutation5
    _ = injectiveMoment H node654 := by rfl

def raw6727 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, 0, -2]]

def raw6727step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 0, 2]]

def raw6727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6727 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6727 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw6727 = injectiveMoment H raw6727step0 := by
      have heq : raw6727step0 = -raw6727 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6727).symm
    injectiveMoment H raw6727step0 = injectiveMoment H raw6727step1 := by
      have heq : raw6727step1 = (fun i j => raw6727step0 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6727step0 permutation31 permutation3
    _ = injectiveMoment H node202 := by rfl

def raw6728 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6728 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6728 = injectiveMoment H node1132 := by
  rfl

def raw6729 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]

def raw6729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6729 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6729 = injectiveMoment H node1132 := by
  calc
    injectiveMoment H raw6729 = injectiveMoment H raw6729step0 := by
      have heq : raw6729step0 = (fun i j => raw6729 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6729 permutation34 permutation3
    _ = injectiveMoment H node1132 := by rfl

def raw6730 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![2, -1, -1]]

def raw6730step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -3, 3], ![-2, 1, 1]]

def raw6730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6730 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6730 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw6730 = injectiveMoment H raw6730step0 := by
      have heq : raw6730step0 = -raw6730 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6730).symm
    injectiveMoment H raw6730step0 = injectiveMoment H raw6730step1 := by
      have heq : raw6730step1 = (fun i j => raw6730step0 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6730step0 permutation31 permutation3
    _ = injectiveMoment H node223 := by rfl

def raw6731 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

theorem canonical6731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6731 = injectiveMoment H node1133 := by
  rfl

def raw6732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical6732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6732 = injectiveMoment H node1134 := by
  rfl

def raw6733 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![2, -2, 0]]

def raw6733step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -4, 4], ![-2, 2, 0]]

def raw6733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical6733 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6733 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw6733 = injectiveMoment H raw6733step0 := by
      have heq : raw6733step0 = -raw6733 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6733).symm
    injectiveMoment H raw6733step0 = injectiveMoment H raw6733step1 := by
      have heq : raw6733step1 = (fun i j => raw6733step0 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6733step0 permutation31 permutation4
    _ = injectiveMoment H node218 := by rfl

def raw6734 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3]]

def raw6734step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -2, 3]]

def raw6734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6734 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6734 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw6734 = injectiveMoment H raw6734step0 := by
      have heq : raw6734step0 = -raw6734 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6734).symm
    injectiveMoment H raw6734step0 = injectiveMoment H raw6734step1 := by
      have heq : raw6734step1 = (fun i j => raw6734step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6734step0 permutation31 permutation5
    _ = injectiveMoment H node175 := by rfl

def raw6735 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6735 = injectiveMoment H node275 := by
  rfl

def raw6736 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1]]

def raw6736step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw6736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6736 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6736 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw6736 = injectiveMoment H raw6736step0 := by
      have heq : raw6736step0 = -raw6736 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6736).symm
    injectiveMoment H raw6736step0 = injectiveMoment H raw6736step1 := by
      have heq : raw6736step1 = (fun i j => raw6736step0 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6736step0 permutation25 permutation5
    _ = injectiveMoment H node175 := by rfl

def raw6737 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0]]

def raw6737step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -3, 4], ![-1, 1, 0]]

def raw6737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6737 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6737 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw6737 = injectiveMoment H raw6737step0 := by
      have heq : raw6737step0 = -raw6737 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6737).symm
    injectiveMoment H raw6737step0 = injectiveMoment H raw6737step1 := by
      have heq : raw6737step1 = (fun i j => raw6737step0 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6737step0 permutation25 permutation3
    _ = injectiveMoment H node244 := by rfl

def raw6738 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 4, -5], ![1, -2, 1]]

def raw6738step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -4, 5], ![-1, 2, -1]]

def raw6738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6738 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6738 = injectiveMoment H node234 := by
  calc
    injectiveMoment H raw6738 = injectiveMoment H raw6738step0 := by
      have heq : raw6738step0 = -raw6738 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6738).symm
    injectiveMoment H raw6738step0 = injectiveMoment H raw6738step1 := by
      have heq : raw6738step1 = (fun i j => raw6738step0 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6738step0 permutation25 permutation3
    _ = injectiveMoment H node234 := by rfl

def raw6739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6739 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6739 = injectiveMoment H node1135 := by
  rfl

def raw6740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw6740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6740 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6740 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw6740 = injectiveMoment H raw6740step0 := by
      have heq : raw6740step0 = (fun i j => raw6740 (permutation36 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6740 permutation36 permutation5
    _ = injectiveMoment H node1151 := by rfl

def raw6741 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]

def raw6741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6741 = injectiveMoment H node659 := by
  calc
    injectiveMoment H raw6741 = injectiveMoment H raw6741step0 := by
      have heq : raw6741step0 = -raw6741 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6741).symm
    injectiveMoment H raw6741step0 = injectiveMoment H raw6741step1 := by
      have heq : raw6741step1 = (fun i j => raw6741step0 (permutation101 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6741step0 permutation101 permutation5
    _ = injectiveMoment H node659 := by rfl

def raw6742 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2]]

def raw6742step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical6742 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6742 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw6742 = injectiveMoment H raw6742step0 := by
      have heq : raw6742step0 = (fun i j => raw6742 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6742 permutation9 permutation5
    _ = injectiveMoment H node283 := by rfl

def raw6743 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6743 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6743 = injectiveMoment H node1141 := by
  rfl

def raw6744 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw6744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6744 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6744 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw6744 = injectiveMoment H raw6744step0 := by
      have heq : raw6744step0 = -raw6744 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6744).symm
    injectiveMoment H raw6744step0 = injectiveMoment H raw6744step1 := by
      have heq : raw6744step1 = (fun i j => raw6744step0 (permutation46 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6744step0 permutation46 permutation7
    _ = injectiveMoment H node711 := by rfl

def raw6745 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical6745 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6745 = injectiveMoment H node1142 := by
  rfl

def raw6746 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw6746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6746 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6746 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw6746 = injectiveMoment H raw6746step0 := by
      have heq : raw6746step0 = (fun i j => raw6746 (permutation89 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6746 permutation89 permutation7
    _ = injectiveMoment H node655 := by rfl

def raw6747 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw6747step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6747 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6747 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw6747 = injectiveMoment H raw6747step0 := by
      have heq : raw6747step0 = (fun i j => raw6747 (permutation30 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6747 permutation30 permutation7
    _ = injectiveMoment H node227 := by rfl

def raw6748 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw6748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2]]

def raw6748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6748 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6748 = injectiveMoment H node1136 := by
  calc
    injectiveMoment H raw6748 = injectiveMoment H raw6748step0 := by
      have heq : raw6748step0 = -raw6748 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6748).symm
    injectiveMoment H raw6748step0 = injectiveMoment H raw6748step1 := by
      have heq : raw6748step1 = (fun i j => raw6748step0 (permutation150 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6748step0 permutation150 permutation3
    _ = injectiveMoment H node1136 := by rfl

def raw6749 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw6749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-1, 0, 1]]

def raw6749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6749 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6749 = injectiveMoment H node1136 := by
  calc
    injectiveMoment H raw6749 = injectiveMoment H raw6749step0 := by
      have heq : raw6749step0 = -raw6749 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6749).symm
    injectiveMoment H raw6749step0 = injectiveMoment H raw6749step1 := by
      have heq : raw6749step1 = (fun i j => raw6749step0 (permutation127 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6749step0 permutation127 permutation3
    _ = injectiveMoment H node1136 := by rfl

def raw6750 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw6750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw6750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6750 = injectiveMoment H node709 := by
  calc
    injectiveMoment H raw6750 = injectiveMoment H raw6750step0 := by
      have heq : raw6750step0 = -raw6750 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6750).symm
    injectiveMoment H raw6750step0 = injectiveMoment H raw6750step1 := by
      have heq : raw6750step1 = (fun i j => raw6750step0 (permutation73 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6750step0 permutation73 permutation5
    _ = injectiveMoment H node709 := by rfl

def raw6751 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw6751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw6751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw6751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6751 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6751 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw6751 = injectiveMoment H raw6751step0 := by
      have heq : raw6751step0 = -raw6751 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6751).symm
    injectiveMoment H raw6751step0 = injectiveMoment H raw6751step1 := by
      have hz : ∀ j, raw6751step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw6751step1 = (fun i j => raw6751step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6751step0 permutation80 hz
    injectiveMoment H raw6751step1 = injectiveMoment H raw6751step2 := by
      have heq : raw6751step2 = (fun i j => raw6751step1 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6751step1 permutation20 permutation5
    _ = injectiveMoment H node230 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
