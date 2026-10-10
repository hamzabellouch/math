import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9728 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9728step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9728step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9728 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9728 = injectiveMoment H node1752 := by
  calc
    injectiveMoment H raw9728 = injectiveMoment H raw9728step0 := by
      have hz : ∀ j, raw9728 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9728step0 = (fun i j => raw9728 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9728 permutation151 hz
    injectiveMoment H raw9728step0 = injectiveMoment H raw9728step1 := by
      have heq : raw9728step1 = (fun i j => raw9728step0 (permutation143 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9728step0 permutation143 permutation17
    _ = injectiveMoment H node1752 := by rfl

def raw9729 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9729step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9729step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical9729 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9729 = injectiveMoment H node2823 := by
  calc
    injectiveMoment H raw9729 = injectiveMoment H raw9729step0 := by
      have hz : ∀ j, raw9729 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9729step0 = (fun i j => raw9729 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9729 permutation151 hz
    injectiveMoment H raw9729step0 = injectiveMoment H raw9729step1 := by
      have heq : raw9729step1 = (fun i j => raw9729step0 (permutation92 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9729step0 permutation92 permutation23
    _ = injectiveMoment H node2823 := by rfl

def raw9730 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9730step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, -1, 2], ![2, 2, 0, -4]]

def raw9730step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, -1, 2], ![2, 2, 0, -4]]

def raw9730step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical9730 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9730 = injectiveMoment H node2596 := by
  calc
    injectiveMoment H raw9730 = injectiveMoment H raw9730step0 := by
      have heq : raw9730step0 = -raw9730 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9730).symm
    injectiveMoment H raw9730step0 = injectiveMoment H raw9730step1 := by
      have hz : ∀ j, raw9730step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9730step1 = (fun i j => raw9730step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9730step0 permutation151 hz
    injectiveMoment H raw9730step1 = injectiveMoment H raw9730step2 := by
      have heq : raw9730step2 = (fun i j => raw9730step1 (permutation105 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9730step1 permutation105 permutation21
    _ = injectiveMoment H node2596 := by rfl

def raw9731 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9731step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9731step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical9731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9731 = injectiveMoment H node2531 := by
  calc
    injectiveMoment H raw9731 = injectiveMoment H raw9731step0 := by
      have hz : ∀ j, raw9731 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9731step0 = (fun i j => raw9731 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9731 permutation151 hz
    injectiveMoment H raw9731step0 = injectiveMoment H raw9731step1 := by
      have heq : raw9731step1 = (fun i j => raw9731step0 (permutation135 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9731step0 permutation135 permutation23
    _ = injectiveMoment H node2531 := by rfl

def raw9732 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9732step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9732step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9732 = injectiveMoment H node1504 := by
  calc
    injectiveMoment H raw9732 = injectiveMoment H raw9732step0 := by
      have hz : ∀ j, raw9732 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9732step0 = (fun i j => raw9732 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9732 permutation151 hz
    injectiveMoment H raw9732step0 = injectiveMoment H raw9732step1 := by
      have heq : raw9732step1 = (fun i j => raw9732step0 (permutation128 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9732step0 permutation128 permutation21
    _ = injectiveMoment H node1504 := by rfl

def raw9733 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9733step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw9733step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw9733step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical9733 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9733 = injectiveMoment H node2627 := by
  calc
    injectiveMoment H raw9733 = injectiveMoment H raw9733step0 := by
      have heq : raw9733step0 = -raw9733 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9733).symm
    injectiveMoment H raw9733step0 = injectiveMoment H raw9733step1 := by
      have hz : ∀ j, raw9733step0 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9733step1 = (fun i j => raw9733step0 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9733step0 permutation151 hz
    injectiveMoment H raw9733step1 = injectiveMoment H raw9733step2 := by
      have heq : raw9733step2 = (fun i j => raw9733step1 (permutation107 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9733step1 permutation107 permutation23
    _ = injectiveMoment H node2627 := by rfl

def raw9734 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9734step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9734step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9734 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9734 = injectiveMoment H node1800 := by
  calc
    injectiveMoment H raw9734 = injectiveMoment H raw9734step0 := by
      have hz : ∀ j, raw9734 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9734step0 = (fun i j => raw9734 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9734 permutation151 hz
    injectiveMoment H raw9734step0 = injectiveMoment H raw9734step1 := by
      have heq : raw9734step1 = (fun i j => raw9734step0 (permutation132 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9734step0 permutation132 permutation11
    _ = injectiveMoment H node1800 := by rfl

def raw9735 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-5, 2, 1, 2], ![5, -2, -2, -1]]

def raw9735step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -5, 5], ![0, 2, -2], ![1, 1, -2], ![-1, 2, -1]]

def raw9735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

theorem canonical9735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9735 = injectiveMoment H node282 := by
  calc
    injectiveMoment H raw9735 = injectiveMoment H raw9735step0 := by
      have heq : raw9735step0 = raw9735.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9735).symm
    injectiveMoment H raw9735step0 = injectiveMoment H raw9735step1 := by
      have heq : raw9735step1 = (fun i j => raw9735step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9735step0 permutation29 permutation4
    _ = injectiveMoment H node282 := by rfl

def raw9736 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-4, 2, 1, 1], ![4, -2, -2, 0]]

def raw9736step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![1, 1, -2], ![-1, 1, 0]]

def raw9736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -2, 2], ![-1, -1, 2], ![1, -1, 0]]

def raw9736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical9736 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9736 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw9736 = injectiveMoment H raw9736step0 := by
      have heq : raw9736step0 = raw9736.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9736).symm
    injectiveMoment H raw9736step0 = injectiveMoment H raw9736step1 := by
      have heq : raw9736step1 = -raw9736step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9736step0).symm
    injectiveMoment H raw9736step1 = injectiveMoment H raw9736step2 := by
      have heq : raw9736step2 = (fun i j => raw9736step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9736step1 permutation23 permutation3
    _ = injectiveMoment H node281 := by rfl

def raw9737 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-4, 3, 1, 0], ![4, -3, -2, 1]]

def raw9737step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 3, -3], ![1, 1, -2], ![-1, 0, 1]]

def raw9737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -3, 3], ![-1, -1, 2], ![1, 0, -1]]

def raw9737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

theorem canonical9737 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9737 = injectiveMoment H node278 := by
  calc
    injectiveMoment H raw9737 = injectiveMoment H raw9737step0 := by
      have heq : raw9737step0 = raw9737.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9737).symm
    injectiveMoment H raw9737step0 = injectiveMoment H raw9737step1 := by
      have heq : raw9737step1 = -raw9737step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9737step0).symm
    injectiveMoment H raw9737step1 = injectiveMoment H raw9737step2 := by
      have heq : raw9737step2 = (fun i j => raw9737step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9737step1 permutation23 permutation3
    _ = injectiveMoment H node278 := by rfl

def raw9738 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 2, -2, 3], ![3, -2, 1, -2]]

def raw9738step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![1, -2, 1], ![-1, 3, -2]]

def raw9738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

theorem canonical9738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9738 = injectiveMoment H node265 := by
  calc
    injectiveMoment H raw9738 = injectiveMoment H raw9738step0 := by
      have heq : raw9738step0 = raw9738.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9738).symm
    injectiveMoment H raw9738step0 = injectiveMoment H raw9738step1 := by
      have heq : raw9738step1 = (fun i j => raw9738step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9738step0 permutation29 permutation4
    _ = injectiveMoment H node265 := by rfl

def raw9739 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 2, 1, 0], ![3, -2, -2, 1]]

def raw9739step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![1, 1, -2], ![-1, 0, 1]]

def raw9739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -2, 2], ![-1, -1, 2], ![1, 0, -1]]

def raw9739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical9739 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9739 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw9739 = injectiveMoment H raw9739step0 := by
      have heq : raw9739step0 = raw9739.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9739).symm
    injectiveMoment H raw9739step0 = injectiveMoment H raw9739step1 := by
      have heq : raw9739step1 = -raw9739step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9739step0).symm
    injectiveMoment H raw9739step1 = injectiveMoment H raw9739step2 := by
      have heq : raw9739step2 = (fun i j => raw9739step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9739step1 permutation23 permutation3
    _ = injectiveMoment H node280 := by rfl

def raw9740 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 3, -2, 2], ![3, -3, 1, -1]]

def raw9740step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![1, -2, 1], ![-1, 2, -1]]

def raw9740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

theorem canonical9740 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9740 = injectiveMoment H node277 := by
  calc
    injectiveMoment H raw9740 = injectiveMoment H raw9740step0 := by
      have heq : raw9740step0 = raw9740.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9740).symm
    injectiveMoment H raw9740step0 = injectiveMoment H raw9740step1 := by
      have heq : raw9740step1 = (fun i j => raw9740step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9740step0 permutation29 permutation4
    _ = injectiveMoment H node277 := by rfl

def raw9741 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 3, 1, -1], ![3, -3, -2, 2]]

def raw9741step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![1, 1, -2], ![-1, -1, 2]]

def raw9741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

theorem canonical9741 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9741 = injectiveMoment H node277 := by
  calc
    injectiveMoment H raw9741 = injectiveMoment H raw9741step0 := by
      have heq : raw9741step0 = raw9741.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9741).symm
    injectiveMoment H raw9741step0 = injectiveMoment H raw9741step1 := by
      have heq : raw9741step1 = (fun i j => raw9741step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9741step0 permutation27 permutation3
    _ = injectiveMoment H node277 := by rfl

def raw9742 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![2, 2, -2, -2]]

def raw9742step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 1, -2], ![-1, 3, -2]]

def raw9742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

theorem canonical9742 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9742 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw9742 = injectiveMoment H raw9742step0 := by
      have heq : raw9742step0 = raw9742.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9742).symm
    injectiveMoment H raw9742step0 = injectiveMoment H raw9742step1 := by
      have heq : raw9742step1 = (fun i j => raw9742step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9742step0 permutation27 permutation4
    _ = injectiveMoment H node274 := by rfl

def raw9743 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![2, -2, 1, -1]]

def raw9743step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![-1, 2, -1]]

def raw9743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical9743 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9743 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw9743 = injectiveMoment H raw9743step0 := by
      have heq : raw9743step0 = raw9743.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9743).symm
    injectiveMoment H raw9743step0 = injectiveMoment H raw9743step1 := by
      have heq : raw9743step1 = (fun i j => raw9743step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9743step0 permutation29 permutation4
    _ = injectiveMoment H node279 := by rfl

def raw9744 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 1, -1], ![2, -2, -2, 2]]

def raw9744step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![-1, -1, 2]]

def raw9744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical9744 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9744 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw9744 = injectiveMoment H raw9744step0 := by
      have heq : raw9744step0 = raw9744.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9744).symm
    injectiveMoment H raw9744step0 = injectiveMoment H raw9744step1 := by
      have heq : raw9744step1 = (fun i j => raw9744step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9744step0 permutation27 permutation3
    _ = injectiveMoment H node279 := by rfl

def raw9745 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 3, -2, 1], ![2, -3, 1, 0]]

def raw9745step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![1, -2, 1], ![-1, 1, 0]]

def raw9745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![-1, 2, -1], ![1, -1, 0]]

def raw9745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical9745 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9745 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw9745 = injectiveMoment H raw9745step0 := by
      have heq : raw9745step0 = raw9745.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9745).symm
    injectiveMoment H raw9745step0 = injectiveMoment H raw9745step1 := by
      have heq : raw9745step1 = -raw9745step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9745step0).symm
    injectiveMoment H raw9745step1 = injectiveMoment H raw9745step2 := by
      have heq : raw9745step2 = (fun i j => raw9745step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9745step1 permutation21 permutation4
    _ = injectiveMoment H node280 := by rfl

def raw9746 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 4, -2, 0], ![2, -4, 1, 1]]

def raw9746step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 4, -4], ![1, -2, 1], ![-1, 0, 1]]

def raw9746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -4, 4], ![-1, 2, -1], ![1, 0, -1]]

def raw9746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical9746 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9746 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw9746 = injectiveMoment H raw9746step0 := by
      have heq : raw9746step0 = raw9746.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9746).symm
    injectiveMoment H raw9746step0 = injectiveMoment H raw9746step1 := by
      have heq : raw9746step1 = -raw9746step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9746step0).symm
    injectiveMoment H raw9746step1 = injectiveMoment H raw9746step2 := by
      have heq : raw9746step2 = (fun i j => raw9746step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9746step1 permutation21 permutation4
    _ = injectiveMoment H node281 := by rfl

def raw9747 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -3, 1, 3], ![1, 3, -2, -2]]

def raw9747step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -3, 3], ![1, 1, -2], ![-1, 3, -2]]

def raw9747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

theorem canonical9747 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9747 = injectiveMoment H node273 := by
  calc
    injectiveMoment H raw9747 = injectiveMoment H raw9747step0 := by
      have heq : raw9747step0 = raw9747.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9747).symm
    injectiveMoment H raw9747step0 = injectiveMoment H raw9747step1 := by
      have heq : raw9747step1 = (fun i j => raw9747step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9747step0 permutation27 permutation4
    _ = injectiveMoment H node273 := by rfl

def raw9748 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -3, 3, 1], ![1, 3, -4, 0]]

def raw9748step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -3, 3], ![1, 3, -4], ![-1, 1, 0]]

def raw9748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 3, -3], ![-1, -3, 4], ![1, -1, 0]]

def raw9748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical9748 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9748 = injectiveMoment H node255 := by
  calc
    injectiveMoment H raw9748 = injectiveMoment H raw9748step0 := by
      have heq : raw9748step0 = raw9748.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9748).symm
    injectiveMoment H raw9748step0 = injectiveMoment H raw9748step1 := by
      have heq : raw9748step1 = -raw9748step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9748step0).symm
    injectiveMoment H raw9748step1 = injectiveMoment H raw9748step2 := by
      have heq : raw9748step2 = (fun i j => raw9748step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9748step1 permutation21 permutation3
    _ = injectiveMoment H node255 := by rfl

def raw9749 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![1, 2, -2, -1]]

def raw9749step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![-1, 2, -1]]

def raw9749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical9749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9749 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw9749 = injectiveMoment H raw9749step0 := by
      have heq : raw9749step0 = raw9749.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9749).symm
    injectiveMoment H raw9749step0 = injectiveMoment H raw9749step1 := by
      have heq : raw9749step1 = (fun i j => raw9749step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9749step0 permutation27 permutation4
    _ = injectiveMoment H node288 := by rfl

def raw9750 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 2, 1], ![1, 2, -3, 0]]

def raw9750step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![-1, 1, 0]]

def raw9750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw9750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical9750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9750 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw9750 = injectiveMoment H raw9750step0 := by
      have heq : raw9750step0 = raw9750.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9750).symm
    injectiveMoment H raw9750step0 = injectiveMoment H raw9750step1 := by
      have heq : raw9750step1 = -raw9750step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9750step0).symm
    injectiveMoment H raw9750step1 = injectiveMoment H raw9750step2 := by
      have heq : raw9750step2 = (fun i j => raw9750step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9750step1 permutation21 permutation3
    _ = injectiveMoment H node272 := by rfl

def raw9751 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 3, 0], ![1, 2, -4, 1]]

def raw9751step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![-1, 0, 1]]

def raw9751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-1, -3, 4], ![1, 0, -1]]

def raw9751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical9751 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9751 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw9751 = injectiveMoment H raw9751step0 := by
      have heq : raw9751step0 = raw9751.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9751).symm
    injectiveMoment H raw9751step0 = injectiveMoment H raw9751step1 := by
      have heq : raw9751step1 = -raw9751step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9751step0).symm
    injectiveMoment H raw9751step1 = injectiveMoment H raw9751step2 := by
      have heq : raw9751step2 = (fun i j => raw9751step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9751step1 permutation21 permutation3
    _ = injectiveMoment H node254 := by rfl

def raw9752 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical9752 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9752 = injectiveMoment H node2750 := by
  calc
    injectiveMoment H raw9752 = injectiveMoment H raw9752step0 := by
      have heq : raw9752step0 = (fun i j => raw9752 (permutation59 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9752 permutation59 permutation13
    _ = injectiveMoment H node2750 := by rfl

def raw9753 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw9753step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![1, 0, -1, 0], ![0, -1, 1, 0], ![-1, 1, 1, -1]]

def raw9753step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9753 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9753 = injectiveMoment H node1118 := by
  calc
    injectiveMoment H raw9753 = injectiveMoment H raw9753step0 := by
      have heq : raw9753step0 = -raw9753 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9753).symm
    injectiveMoment H raw9753step0 = injectiveMoment H raw9753step1 := by
      have heq : raw9753step1 = (fun i j => raw9753step0 (permutation31 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9753step0 permutation31 permutation13
    _ = injectiveMoment H node1118 := by rfl

def raw9754 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical9754 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9754 = injectiveMoment H node2823 := by
  calc
    injectiveMoment H raw9754 = injectiveMoment H raw9754step0 := by
      have heq : raw9754step0 = (fun i j => raw9754 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9754 permutation57 permutation9
    _ = injectiveMoment H node2823 := by rfl

def raw9755 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw9755step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![1, 1, 0, -2], ![-1, 0, -2, 3]]

def raw9755step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![-1, -1, 0, 2], ![1, 0, 2, -3]]

def raw9755step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical9755 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9755 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw9755 = injectiveMoment H raw9755step0 := by
      have heq : raw9755step0 = raw9755.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9755).symm
    injectiveMoment H raw9755step0 = injectiveMoment H raw9755step1 := by
      have heq : raw9755step1 = -raw9755step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9755step0).symm
    injectiveMoment H raw9755step1 = injectiveMoment H raw9755step2 := by
      have heq : raw9755step2 = (fun i j => raw9755step1 (permutation23 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9755step1 permutation23 permutation9
    _ = injectiveMoment H node1032 := by rfl

def raw9756 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9756step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 1, 0, -2], ![-1, -1, -1, 3]]

def raw9756step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical9756 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9756 = injectiveMoment H node964 := by
  calc
    injectiveMoment H raw9756 = injectiveMoment H raw9756step0 := by
      have heq : raw9756step0 = raw9756.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9756).symm
    injectiveMoment H raw9756step0 = injectiveMoment H raw9756step1 := by
      have heq : raw9756step1 = (fun i j => raw9756step0 (permutation27 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9756step0 permutation27 permutation11
    _ = injectiveMoment H node964 := by rfl

def raw9757 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 2, -2, 1], ![1, -2, 1, 0]]

def raw9757step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![-1, 1, 0]]

def raw9757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0]]

def raw9757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical9757 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9757 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw9757 = injectiveMoment H raw9757step0 := by
      have heq : raw9757step0 = raw9757.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9757).symm
    injectiveMoment H raw9757step0 = injectiveMoment H raw9757step1 := by
      have heq : raw9757step1 = -raw9757step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9757step0).symm
    injectiveMoment H raw9757step1 = injectiveMoment H raw9757step2 := by
      have heq : raw9757step2 = (fun i j => raw9757step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9757step1 permutation21 permutation4
    _ = injectiveMoment H node284 := by rfl

def raw9758 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -2, -2, 3]]

def raw9758step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw9758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical9758 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9758 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw9758 = injectiveMoment H raw9758step0 := by
      have heq : raw9758step0 = raw9758.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9758).symm
    injectiveMoment H raw9758step0 = injectiveMoment H raw9758step1 := by
      have heq : raw9758step1 = (fun i j => raw9758step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9758step0 permutation27 permutation3
    _ = injectiveMoment H node268 := by rfl

def raw9759 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 3, -2, 0], ![1, -3, 1, 1]]

def raw9759step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![-1, 0, 1]]

def raw9759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -3, 3], ![-1, 2, -1], ![1, 0, -1]]

def raw9759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical9759 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9759 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw9759 = injectiveMoment H raw9759step0 := by
      have heq : raw9759step0 = raw9759.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9759).symm
    injectiveMoment H raw9759step0 = injectiveMoment H raw9759step1 := by
      have heq : raw9759step1 = -raw9759step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9759step0).symm
    injectiveMoment H raw9759step1 = injectiveMoment H raw9759step2 := by
      have heq : raw9759step2 = (fun i j => raw9759step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9759step1 permutation21 permutation4
    _ = injectiveMoment H node285 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
