import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def raw768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

theorem canonical768 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw768 = injectiveMoment H node1891 := by
  calc
    injectiveMoment H raw768 = injectiveMoment H raw768step0 := by
      have heq : raw768step0 = -raw768 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw768).symm
    injectiveMoment H raw768step0 = injectiveMoment H raw768step1 := by
      have heq : raw768step1 = (fun i j => raw768step0 (permutation180 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw768step0 permutation180 permutation8
    _ = injectiveMoment H node1891 := by rfl

def raw769 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]

def raw769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical769 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw769 = injectiveMoment H node573 := by
  calc
    injectiveMoment H raw769 = injectiveMoment H raw769step0 := by
      have heq : raw769step0 = -raw769 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw769).symm
    injectiveMoment H raw769step0 = injectiveMoment H raw769step1 := by
      have heq : raw769step1 = (fun i j => raw769step0 (permutation49 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw769step0 permutation49 permutation8
    _ = injectiveMoment H node573 := by rfl

def raw770 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw770 = injectiveMoment H node372 := by
  calc
    injectiveMoment H raw770 = injectiveMoment H raw770step0 := by
      have heq : raw770step0 = (fun i j => raw770 (permutation148 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw770 permutation148 permutation6
    _ = injectiveMoment H node372 := by rfl

def raw771 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

def raw771step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]

def raw771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical771 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw771 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw771 = injectiveMoment H raw771step0 := by
      have heq : raw771step0 = -raw771 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw771).symm
    injectiveMoment H raw771step0 = injectiveMoment H raw771step1 := by
      have heq : raw771step1 = (fun i j => raw771step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw771step0 permutation13 permutation8
    _ = injectiveMoment H node188 := by rfl

def raw772 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]

def raw772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]

theorem canonical772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw772 = injectiveMoment H node379 := by
  calc
    injectiveMoment H raw772 = injectiveMoment H raw772step0 := by
      have heq : raw772step0 = (fun i j => raw772 (permutation39 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw772 permutation39 permutation4
    _ = injectiveMoment H node379 := by rfl

def raw773 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw773 = injectiveMoment H node375 := by
  rfl

def raw774 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]

def raw774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical774 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw774 = injectiveMoment H node375 := by
  calc
    injectiveMoment H raw774 = injectiveMoment H raw774step0 := by
      have heq : raw774step0 = (fun i j => raw774 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw774 permutation34 permutation3
    _ = injectiveMoment H node375 := by rfl

def raw775 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

theorem canonical775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw775 = injectiveMoment H node108 := by
  rfl

def raw776 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw776 = injectiveMoment H node376 := by
  rfl

def raw777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical777 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw777 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw777 = injectiveMoment H raw777step0 := by
      have heq : raw777step0 = (fun i j => raw777 (permutation97 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw777 permutation97 permutation6
    _ = injectiveMoment H node708 := by rfl

def raw778 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw778 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw778 = injectiveMoment H raw778step0 := by
      have heq : raw778step0 = (fun i j => raw778 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw778 permutation26 permutation6
    _ = injectiveMoment H node226 := by rfl

def raw779 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]

def raw779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical779 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw779 = injectiveMoment H node376 := by
  calc
    injectiveMoment H raw779 = injectiveMoment H raw779step0 := by
      have heq : raw779step0 = (fun i j => raw779 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw779 permutation35 permutation3
    _ = injectiveMoment H node376 := by rfl

def raw780 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical780 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw780 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw780 = injectiveMoment H raw780step0 := by
      have heq : raw780step0 = -raw780 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw780).symm
    injectiveMoment H raw780step0 = injectiveMoment H raw780step1 := by
      have heq : raw780step1 = (fun i j => raw780step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw780step0 permutation41 permutation8
    _ = injectiveMoment H node570 := by rfl

def raw781 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw781step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw781 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw781 = injectiveMoment H raw781step0 := by
      have heq : raw781step0 = -raw781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw781).symm
    injectiveMoment H raw781step0 = injectiveMoment H raw781step1 := by
      have heq : raw781step1 = (fun i j => raw781step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw781step0 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

def raw782 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw782step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw782 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw782 = injectiveMoment H raw782step0 := by
      have heq : raw782step0 = -raw782 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw782).symm
    injectiveMoment H raw782step0 = injectiveMoment H raw782step1 := by
      have heq : raw782step1 = (fun i j => raw782step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw782step0 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

def raw783 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw783 = injectiveMoment H node109 := by
  rfl

def raw784 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]

def raw784step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw784step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw784 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw784 = injectiveMoment H raw784step0 := by
      have heq : raw784step0 = raw784.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw784).symm
    injectiveMoment H raw784step0 = injectiveMoment H raw784step1 := by
      have heq : raw784step1 = (fun i j => raw784step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw784step0 permutation7 permutation6
    _ = injectiveMoment H node63 := by rfl

def raw785 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

theorem canonical785 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw785 = injectiveMoment H node373 := by
  calc
    injectiveMoment H raw785 = injectiveMoment H raw785step0 := by
      have heq : raw785step0 = (fun i j => raw785 (permutation96 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw785 permutation96 permutation5
    _ = injectiveMoment H node373 := by rfl

def raw786 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

theorem canonical786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw786 = injectiveMoment H node110 := by
  rfl

def raw787 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical787 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw787 = injectiveMoment H node377 := by
  rfl

def raw788 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0]]

def raw788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical788 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw788 = injectiveMoment H node377 := by
  calc
    injectiveMoment H raw788 = injectiveMoment H raw788step0 := by
      have heq : raw788step0 = (fun i j => raw788 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw788 permutation34 permutation3
    _ = injectiveMoment H node377 := by rfl

def raw789 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw789 = injectiveMoment H node111 := by
  rfl

def raw790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]

def raw790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical790 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw790 = injectiveMoment H node377 := by
  calc
    injectiveMoment H raw790 = injectiveMoment H raw790step0 := by
      have heq : raw790step0 = (fun i j => raw790 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw790 permutation35 permutation3
    _ = injectiveMoment H node377 := by rfl

def raw791 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def raw791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical791 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw791 = injectiveMoment H node566 := by
  calc
    injectiveMoment H raw791 = injectiveMoment H raw791step0 := by
      have heq : raw791step0 = -raw791 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw791).symm
    injectiveMoment H raw791step0 = injectiveMoment H raw791step1 := by
      have heq : raw791step1 = (fun i j => raw791step0 (permutation42 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw791step0 permutation42 permutation8
    _ = injectiveMoment H node566 := by rfl

def raw792 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw792step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]

def raw792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw792 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw792 = injectiveMoment H raw792step0 := by
      have heq : raw792step0 = -raw792 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw792).symm
    injectiveMoment H raw792step0 = injectiveMoment H raw792step1 := by
      have heq : raw792step1 = (fun i j => raw792step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw792step0 permutation12 permutation8
    _ = injectiveMoment H node177 := by rfl

def raw793 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

def raw793step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical793 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw793 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw793 = injectiveMoment H raw793step0 := by
      have heq : raw793step0 = (fun i j => raw793 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw793 permutation31 permutation6
    _ = injectiveMoment H node107 := by rfl

def raw794 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]

def raw794step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw794 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw794 = injectiveMoment H raw794step0 := by
      have heq : raw794step0 = (fun i j => raw794 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw794 permutation25 permutation6
    _ = injectiveMoment H node107 := by rfl

def raw795 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]

def raw795step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-3, 3, 0]]

def raw795step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical795 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw795 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw795 = injectiveMoment H raw795step0 := by
      have heq : raw795step0 = -raw795 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw795).symm
    injectiveMoment H raw795step0 = injectiveMoment H raw795step1 := by
      have heq : raw795step1 = (fun i j => raw795step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw795step0 permutation4 permutation8
    _ = injectiveMoment H node37 := by rfl

def raw796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

theorem canonical796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw796 = injectiveMoment H node373 := by
  calc
    injectiveMoment H raw796 = injectiveMoment H raw796step0 := by
      have heq : raw796step0 = (fun i j => raw796 (permutation72 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw796 permutation72 permutation5
    _ = injectiveMoment H node373 := by rfl

def raw797 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![0, 2, -2], ![2, 0, -2]]

def raw797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

theorem canonical797 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw797 = injectiveMoment H node110 := by
  calc
    injectiveMoment H raw797 = injectiveMoment H raw797step0 := by
      have heq : raw797step0 = (fun i j => raw797 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw797 permutation11 permutation3
    _ = injectiveMoment H node110 := by rfl

def raw798 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw798 = injectiveMoment H node113 := by
  rfl

def raw799 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

def raw799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

theorem canonical799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw799 = injectiveMoment H node108 := by
  calc
    injectiveMoment H raw799 = injectiveMoment H raw799step0 := by
      have heq : raw799step0 = (fun i j => raw799 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw799 permutation17 permutation5
    _ = injectiveMoment H node108 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
