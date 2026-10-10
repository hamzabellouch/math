import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3776 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, -1, 1]]

def raw3776step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, -1, -1, 1]]

def raw3776step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3776 = injectiveMoment H node1112 := by
  calc
    injectiveMoment H raw3776 = injectiveMoment H raw3776step0 := by
      have heq : raw3776step0 = raw3776.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3776).symm
    injectiveMoment H raw3776step0 = injectiveMoment H raw3776step1 := by
      have heq : raw3776step1 = (fun i j => raw3776step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3776step0 permutation27 permutation17
    _ = injectiveMoment H node1112 := by rfl

def raw3777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw3777step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 3, -3], ![-1, -1, -1, 3]]

def raw3777step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem canonical3777 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3777 = injectiveMoment H node965 := by
  calc
    injectiveMoment H raw3777 = injectiveMoment H raw3777step0 := by
      have heq : raw3777step0 = -raw3777 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3777).symm
    injectiveMoment H raw3777step0 = injectiveMoment H raw3777step1 := by
      have heq : raw3777step1 = (fun i j => raw3777step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3777step0 permutation29 permutation15
    _ = injectiveMoment H node965 := by rfl

def raw3778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3778step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3778step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical3778 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3778 = injectiveMoment H node1246 := by
  calc
    injectiveMoment H raw3778 = injectiveMoment H raw3778step0 := by
      have heq : raw3778step0 = -raw3778 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3778).symm
    injectiveMoment H raw3778step0 = injectiveMoment H raw3778step1 := by
      have heq : raw3778step1 = (fun i j => raw3778step0 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3778step0 permutation27 permutation19
    _ = injectiveMoment H node1246 := by rfl

def raw3779 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw3779step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 3, -1]]

def raw3779step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical3779 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3779 = injectiveMoment H node942 := by
  calc
    injectiveMoment H raw3779 = injectiveMoment H raw3779step0 := by
      have heq : raw3779step0 = -raw3779 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3779).symm
    injectiveMoment H raw3779step0 = injectiveMoment H raw3779step1 := by
      have heq : raw3779step1 = (fun i j => raw3779step0 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3779step0 permutation27 permutation19
    _ = injectiveMoment H node942 := by rfl

def raw3780 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def raw3780step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-2, 1, 1, 0]]

def raw3780step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3780 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3780 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw3780 = injectiveMoment H raw3780step0 := by
      have heq : raw3780step0 = -raw3780 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3780).symm
    injectiveMoment H raw3780step0 = injectiveMoment H raw3780step1 := by
      have heq : raw3780step1 = (fun i j => raw3780step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3780step0 permutation21 permutation19
    _ = injectiveMoment H node1010 := by rfl

def raw3781 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, -2, 1]]

def raw3781step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 1, 2, -1]]

def raw3781step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3781 = injectiveMoment H node1281 := by
  calc
    injectiveMoment H raw3781 = injectiveMoment H raw3781step0 := by
      have heq : raw3781step0 = -raw3781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3781).symm
    injectiveMoment H raw3781step0 = injectiveMoment H raw3781step1 := by
      have heq : raw3781step1 = (fun i j => raw3781step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3781step0 permutation21 permutation19
    _ = injectiveMoment H node1281 := by rfl

def raw3782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, -2, 2]]

def raw3782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, 2, -1, -2], ![1, -2, -1, 2]]

def raw3782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]

theorem canonical3782 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3782 = injectiveMoment H node506 := by
  calc
    injectiveMoment H raw3782 = injectiveMoment H raw3782step0 := by
      have heq : raw3782step0 = raw3782.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3782).symm
    injectiveMoment H raw3782step0 = injectiveMoment H raw3782step1 := by
      have heq : raw3782step1 = (fun i j => raw3782step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3782step0 permutation27 permutation17
    _ = injectiveMoment H node506 := by rfl

def raw3783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw3783step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![-1, 1, 3, -3], ![-1, -1, 0, 2]]

def raw3783step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem canonical3783 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3783 = injectiveMoment H node1035 := by
  calc
    injectiveMoment H raw3783 = injectiveMoment H raw3783step0 := by
      have heq : raw3783step0 = -raw3783 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3783).symm
    injectiveMoment H raw3783step0 = injectiveMoment H raw3783step1 := by
      have heq : raw3783step1 = (fun i j => raw3783step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3783step0 permutation29 permutation15
    _ = injectiveMoment H node1035 := by rfl

def raw3784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw3784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![-1, 1, 1, -1], ![-1, -1, 2, 0]]

def raw3784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3784 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3784 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw3784 = injectiveMoment H raw3784step0 := by
      have heq : raw3784step0 = -raw3784 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3784).symm
    injectiveMoment H raw3784step0 = injectiveMoment H raw3784step1 := by
      have heq : raw3784step1 = (fun i j => raw3784step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3784step0 permutation29 permutation16
    _ = injectiveMoment H node1058 := by rfl

def raw3785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw3785step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 3, -1]]

def raw3785step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3785 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3785 = injectiveMoment H node946 := by
  calc
    injectiveMoment H raw3785 = injectiveMoment H raw3785step0 := by
      have heq : raw3785step0 = -raw3785 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3785).symm
    injectiveMoment H raw3785step0 = injectiveMoment H raw3785step1 := by
      have heq : raw3785step1 = (fun i j => raw3785step0 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3785step0 permutation27 permutation19
    _ = injectiveMoment H node946 := by rfl

def raw3786 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical3786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3786 = injectiveMoment H node2086 := by
  rfl

def raw3787 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3787step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -3, 0, 2], ![1, 2, -1, -2]]

def raw3787step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 3, 0, -2], ![-1, -2, 1, 2]]

def raw3787step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3787 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3787 = injectiveMoment H node1250 := by
  calc
    injectiveMoment H raw3787 = injectiveMoment H raw3787step0 := by
      have heq : raw3787step0 = raw3787.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3787).symm
    injectiveMoment H raw3787step0 = injectiveMoment H raw3787step1 := by
      have heq : raw3787step1 = -raw3787step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3787step0).symm
    injectiveMoment H raw3787step1 = injectiveMoment H raw3787step2 := by
      have heq : raw3787step2 = (fun i j => raw3787step1 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3787step1 permutation17 permutation21
    _ = injectiveMoment H node1250 := by rfl

def raw3788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3788step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -3, 1, 1], ![1, 2, -2, -1]]

def raw3788step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

theorem canonical3788 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3788 = injectiveMoment H node612 := by
  calc
    injectiveMoment H raw3788 = injectiveMoment H raw3788step0 := by
      have heq : raw3788step0 = raw3788.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3788).symm
    injectiveMoment H raw3788step0 = injectiveMoment H raw3788step1 := by
      have heq : raw3788step1 = (fun i j => raw3788step0 (permutation10 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3788step0 permutation10 permutation11
    _ = injectiveMoment H node612 := by rfl

def raw3789 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 1, 2, -4]]

theorem canonical3789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3789 = injectiveMoment H node615 := by
  rfl

def raw3790 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

theorem canonical3790 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3790 = injectiveMoment H node616 := by
  rfl

def raw3791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 1, 0, -2]]

theorem canonical3791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3791 = injectiveMoment H node617 := by
  rfl

def raw3792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3792step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 3, -2], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw3792step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical3792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3792 = injectiveMoment H node1214 := by
  calc
    injectiveMoment H raw3792 = injectiveMoment H raw3792step0 := by
      have heq : raw3792step0 = -raw3792 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3792).symm
    injectiveMoment H raw3792step0 = injectiveMoment H raw3792step1 := by
      have heq : raw3792step1 = (fun i j => raw3792step0 (permutation19 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3792step0 permutation19 permutation16
    _ = injectiveMoment H node1214 := by rfl

def raw3793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 3, -2], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw3793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical3793 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3793 = injectiveMoment H node1208 := by
  calc
    injectiveMoment H raw3793 = injectiveMoment H raw3793step0 := by
      have heq : raw3793step0 = -raw3793 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3793).symm
    injectiveMoment H raw3793step0 = injectiveMoment H raw3793step1 := by
      have heq : raw3793step1 = (fun i j => raw3793step0 (permutation19 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3793step0 permutation19 permutation16
    _ = injectiveMoment H node1208 := by rfl

def raw3794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3794step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 3, -2], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw3794step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical3794 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3794 = injectiveMoment H node1204 := by
  calc
    injectiveMoment H raw3794 = injectiveMoment H raw3794step0 := by
      have heq : raw3794step0 = -raw3794 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3794).symm
    injectiveMoment H raw3794step0 = injectiveMoment H raw3794step1 := by
      have heq : raw3794step1 = (fun i j => raw3794step0 (permutation19 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3794step0 permutation19 permutation16
    _ = injectiveMoment H node1204 := by rfl

def raw3795 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3795step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical3795 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3795 = injectiveMoment H node1745 := by
  calc
    injectiveMoment H raw3795 = injectiveMoment H raw3795step0 := by
      have heq : raw3795step0 = (fun i j => raw3795 (permutation123 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3795 permutation123 permutation19
    _ = injectiveMoment H node1745 := by rfl

def raw3796 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3796step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw3796step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical3796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3796 = injectiveMoment H node828 := by
  calc
    injectiveMoment H raw3796 = injectiveMoment H raw3796step0 := by
      have heq : raw3796step0 = raw3796.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3796).symm
    injectiveMoment H raw3796step0 = injectiveMoment H raw3796step1 := by
      have heq : raw3796step1 = (fun i j => raw3796step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3796step0 permutation22 permutation23
    _ = injectiveMoment H node828 := by rfl

def raw3797 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3797step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical3797 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3797 = injectiveMoment H node2073 := by
  calc
    injectiveMoment H raw3797 = injectiveMoment H raw3797step0 := by
      have heq : raw3797step0 = (fun i j => raw3797 (permutation123 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3797 permutation123 permutation20
    _ = injectiveMoment H node2073 := by rfl

def raw3798 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3798step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical3798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3798 = injectiveMoment H node1784 := by
  calc
    injectiveMoment H raw3798 = injectiveMoment H raw3798step0 := by
      have heq : raw3798step0 = (fun i j => raw3798 (permutation123 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3798 permutation123 permutation19
    _ = injectiveMoment H node1784 := by rfl

def raw3799 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3799step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical3799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3799 = injectiveMoment H node2084 := by
  calc
    injectiveMoment H raw3799 = injectiveMoment H raw3799step0 := by
      have heq : raw3799step0 = (fun i j => raw3799 (permutation64 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3799 permutation64 permutation22
    _ = injectiveMoment H node2084 := by rfl

def raw3800 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical3800 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3800 = injectiveMoment H node2087 := by
  rfl

def raw3801 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw3801step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -1, -1, 2], ![-2, 2, 0, 0]]

def raw3801step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3801 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3801 = injectiveMoment H node609 := by
  calc
    injectiveMoment H raw3801 = injectiveMoment H raw3801step0 := by
      have heq : raw3801step0 = -raw3801 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3801).symm
    injectiveMoment H raw3801step0 = injectiveMoment H raw3801step1 := by
      have heq : raw3801step1 = (fun i j => raw3801step0 (permutation32 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3801step0 permutation32 permutation12
    _ = injectiveMoment H node609 := by rfl

def raw3802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw3802step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

theorem canonical3802 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3802 = injectiveMoment H node612 := by
  calc
    injectiveMoment H raw3802 = injectiveMoment H raw3802step0 := by
      have heq : raw3802step0 = raw3802.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3802).symm
    _ = injectiveMoment H node612 := by rfl

def raw3803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

theorem canonical3803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3803 = injectiveMoment H node618 := by
  rfl

def raw3804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

theorem canonical3804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3804 = injectiveMoment H node619 := by
  rfl

def raw3805 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3805step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical3805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3805 = injectiveMoment H node513 := by
  calc
    injectiveMoment H raw3805 = injectiveMoment H raw3805step0 := by
      have heq : raw3805step0 = (fun i j => raw3805 (permutation22 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3805 permutation22 permutation19
    _ = injectiveMoment H node513 := by rfl

def raw3806 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3806step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw3806step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3806 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3806 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw3806 = injectiveMoment H raw3806step0 := by
      have heq : raw3806step0 = -raw3806 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3806).symm
    injectiveMoment H raw3806step0 = injectiveMoment H raw3806step1 := by
      have heq : raw3806step1 = (fun i j => raw3806step0 (permutation16 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3806step0 permutation16 permutation19
    _ = injectiveMoment H node1009 := by rfl

def raw3807 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3807step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw3807step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical3807 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3807 = injectiveMoment H node1006 := by
  calc
    injectiveMoment H raw3807 = injectiveMoment H raw3807step0 := by
      have heq : raw3807step0 = -raw3807 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3807).symm
    injectiveMoment H raw3807step0 = injectiveMoment H raw3807step1 := by
      have heq : raw3807step1 = (fun i j => raw3807step0 (permutation16 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3807step0 permutation16 permutation19
    _ = injectiveMoment H node1006 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
