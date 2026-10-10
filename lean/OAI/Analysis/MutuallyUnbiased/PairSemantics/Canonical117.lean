import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3744step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, 1, -2, 3]]

def raw3744step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

theorem canonical3744 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3744 = injectiveMoment H node2782 := by
  calc
    injectiveMoment H raw3744 = injectiveMoment H raw3744step0 := by
      have heq : raw3744step0 = -raw3744 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3744).symm
    injectiveMoment H raw3744step0 = injectiveMoment H raw3744step1 := by
      have heq : raw3744step1 = (fun i j => raw3744step0 (permutation112 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3744step0 permutation112 permutation16
    _ = injectiveMoment H node2782 := by rfl

def raw3745 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3745step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw3745step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical3745 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3745 = injectiveMoment H node2504 := by
  calc
    injectiveMoment H raw3745 = injectiveMoment H raw3745step0 := by
      have heq : raw3745step0 = -raw3745 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3745).symm
    injectiveMoment H raw3745step0 = injectiveMoment H raw3745step1 := by
      have heq : raw3745step1 = (fun i j => raw3745step0 (permutation135 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3745step0 permutation135 permutation15
    _ = injectiveMoment H node2504 := by rfl

def raw3746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3746step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw3746step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical3746 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3746 = injectiveMoment H node2542 := by
  calc
    injectiveMoment H raw3746 = injectiveMoment H raw3746step0 := by
      have heq : raw3746step0 = -raw3746 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3746).symm
    injectiveMoment H raw3746step0 = injectiveMoment H raw3746step1 := by
      have heq : raw3746step1 = (fun i j => raw3746step0 (permutation128 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3746step0 permutation128 permutation17
    _ = injectiveMoment H node2542 := by rfl

def raw3747 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

theorem canonical3747 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3747 = injectiveMoment H node2081 := by
  rfl

def raw3748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![2, -1, 2, -3]]

def raw3748step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-2, 1, -2, 3]]

def raw3748step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

theorem canonical3748 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3748 = injectiveMoment H node2782 := by
  calc
    injectiveMoment H raw3748 = injectiveMoment H raw3748step0 := by
      have heq : raw3748step0 = -raw3748 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3748).symm
    injectiveMoment H raw3748step0 = injectiveMoment H raw3748step1 := by
      have heq : raw3748step1 = (fun i j => raw3748step0 (permutation88 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3748step0 permutation88 permutation16
    _ = injectiveMoment H node2782 := by rfl

def raw3749 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3749step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical3749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3749 = injectiveMoment H node1523 := by
  calc
    injectiveMoment H raw3749 = injectiveMoment H raw3749step0 := by
      have heq : raw3749step0 = (fun i j => raw3749 (permutation128 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3749 permutation128 permutation19
    _ = injectiveMoment H node1523 := by rfl

def raw3750 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3750step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw3750step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical3750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3750 = injectiveMoment H node1786 := by
  calc
    injectiveMoment H raw3750 = injectiveMoment H raw3750step0 := by
      have heq : raw3750step0 = -raw3750 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3750).symm
    injectiveMoment H raw3750step0 = injectiveMoment H raw3750step1 := by
      have heq : raw3750step1 = (fun i j => raw3750step0 (permutation148 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3750step0 permutation148 permutation12
    _ = injectiveMoment H node1786 := by rfl

def raw3751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 2, -4]]

theorem canonical3751 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3751 = injectiveMoment H node2083 := by
  rfl

def raw3752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical3752 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3752 = injectiveMoment H node2069 := by
  calc
    injectiveMoment H raw3752 = injectiveMoment H raw3752step0 := by
      have heq : raw3752step0 = (fun i j => raw3752 (permutation110 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3752 permutation110 permutation17
    _ = injectiveMoment H node2069 := by rfl

def raw3753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3753step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw3753step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3753 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3753 = injectiveMoment H node2779 := by
  calc
    injectiveMoment H raw3753 = injectiveMoment H raw3753step0 := by
      have heq : raw3753step0 = -raw3753 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3753).symm
    injectiveMoment H raw3753step0 = injectiveMoment H raw3753step1 := by
      have heq : raw3753step1 = (fun i j => raw3753step0 (permutation100 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3753step0 permutation100 permutation16
    _ = injectiveMoment H node2779 := by rfl

def raw3754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3754 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3754 = injectiveMoment H node2744 := by
  calc
    injectiveMoment H raw3754 = injectiveMoment H raw3754step0 := by
      have heq : raw3754step0 = (fun i j => raw3754 (permutation124 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3754 permutation124 permutation20
    _ = injectiveMoment H node2744 := by rfl

def raw3755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3755step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3755 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3755 = injectiveMoment H node2632 := by
  calc
    injectiveMoment H raw3755 = injectiveMoment H raw3755step0 := by
      have heq : raw3755step0 = (fun i j => raw3755 (permutation124 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3755 permutation124 permutation20
    _ = injectiveMoment H node2632 := by rfl

def raw3756 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3756step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical3756 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3756 = injectiveMoment H node2645 := by
  calc
    injectiveMoment H raw3756 = injectiveMoment H raw3756step0 := by
      have heq : raw3756step0 = (fun i j => raw3756 (permutation124 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3756 permutation124 permutation20
    _ = injectiveMoment H node2645 := by rfl

def raw3757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3757step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3757step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical3757 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3757 = injectiveMoment H node2588 := by
  calc
    injectiveMoment H raw3757 = injectiveMoment H raw3757step0 := by
      have heq : raw3757step0 = -raw3757 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3757).symm
    injectiveMoment H raw3757step0 = injectiveMoment H raw3757step1 := by
      have heq : raw3757step1 = (fun i j => raw3757step0 (permutation84 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3757step0 permutation84 permutation17
    _ = injectiveMoment H node2588 := by rfl

def raw3758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw3758step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-1, 1, 2, -2], ![-1, -1, -2, 4]]

def raw3758step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical3758 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3758 = injectiveMoment H node911 := by
  calc
    injectiveMoment H raw3758 = injectiveMoment H raw3758step0 := by
      have heq : raw3758step0 = -raw3758 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3758).symm
    injectiveMoment H raw3758step0 = injectiveMoment H raw3758step1 := by
      have heq : raw3758step1 = (fun i j => raw3758step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3758step0 permutation29 permutation15
    _ = injectiveMoment H node911 := by rfl

def raw3759 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3759step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw3759step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical3759 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3759 = injectiveMoment H node942 := by
  calc
    injectiveMoment H raw3759 = injectiveMoment H raw3759step0 := by
      have heq : raw3759step0 = -raw3759 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3759).symm
    injectiveMoment H raw3759step0 = injectiveMoment H raw3759step1 := by
      have heq : raw3759step1 = (fun i j => raw3759step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3759step0 permutation27 permutation17
    _ = injectiveMoment H node942 := by rfl

def raw3760 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3760step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw3760step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical3760 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3760 = injectiveMoment H node1119 := by
  calc
    injectiveMoment H raw3760 = injectiveMoment H raw3760step0 := by
      have heq : raw3760step0 = -raw3760 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3760).symm
    injectiveMoment H raw3760step0 = injectiveMoment H raw3760step1 := by
      have heq : raw3760step1 = (fun i j => raw3760step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3760step0 permutation29 permutation16
    _ = injectiveMoment H node1119 := by rfl

def raw3761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 0, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3761step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![1, 0, -2, 0, 1], ![1, 0, 1, -1, -1]]

def raw3761step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![0, 0, -1, -1, 2], ![-1, 0, 2, 0, -1], ![-1, 0, -1, 1, 1]]

def raw3761step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 2, 0, -1], ![-1, -1, 1, 1]]

def raw3761step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3761 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3761 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw3761 = injectiveMoment H raw3761step0 := by
      have heq : raw3761step0 = raw3761.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3761).symm
    injectiveMoment H raw3761step0 = injectiveMoment H raw3761step1 := by
      have heq : raw3761step1 = -raw3761step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3761step0).symm
    injectiveMoment H raw3761step1 = injectiveMoment H raw3761step2 := by
      have hz : ∀ i, raw3761step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw3761step2 = (fun i j => raw3761step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3761step1 permutation57 hz
    injectiveMoment H raw3761step2 = injectiveMoment H raw3761step3 := by
      have heq : raw3761step3 = (fun i j => raw3761step2 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3761step2 permutation15 permutation23
    _ = injectiveMoment H node1058 := by rfl

def raw3762 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3762step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw3762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]

def raw3762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3762 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3762 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw3762 = injectiveMoment H raw3762step0 := by
      have heq : raw3762step0 = raw3762.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3762).symm
    injectiveMoment H raw3762step0 = injectiveMoment H raw3762step1 := by
      have hz : ∀ i, raw3762step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw3762step1 = (fun i j => raw3762step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3762step0 permutation15 hz
    injectiveMoment H raw3762step1 = injectiveMoment H raw3762step2 := by
      have heq : raw3762step2 = (fun i j => raw3762step1 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3762step1 permutation10 permutation3
    _ = injectiveMoment H node230 := by rfl

def raw3763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3763step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw3763step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw3763step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical3763 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3763 = injectiveMoment H node1119 := by
  calc
    injectiveMoment H raw3763 = injectiveMoment H raw3763step0 := by
      have heq : raw3763step0 = -raw3763 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3763).symm
    injectiveMoment H raw3763step0 = injectiveMoment H raw3763step1 := by
      have hz : ∀ j, raw3763step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3763step1 = (fun i j => raw3763step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3763step0 permutation80 hz
    injectiveMoment H raw3763step1 = injectiveMoment H raw3763step2 := by
      have heq : raw3763step2 = (fun i j => raw3763step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3763step1 permutation29 permutation15
    _ = injectiveMoment H node1119 := by rfl

def raw3764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3764step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3764step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical3764 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3764 = injectiveMoment H node1246 := by
  calc
    injectiveMoment H raw3764 = injectiveMoment H raw3764step0 := by
      have heq : raw3764step0 = -raw3764 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3764).symm
    injectiveMoment H raw3764step0 = injectiveMoment H raw3764step1 := by
      have hz : ∀ j, raw3764step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3764step1 = (fun i j => raw3764step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3764step0 permutation80 hz
    injectiveMoment H raw3764step1 = injectiveMoment H raw3764step2 := by
      have heq : raw3764step2 = (fun i j => raw3764step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3764step1 permutation27 permutation19
    _ = injectiveMoment H node1246 := by rfl

def raw3765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -1, 1]]

theorem canonical3765 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3765 = injectiveMoment H node2082 := by
  calc
    injectiveMoment H raw3765 = injectiveMoment H raw3765step0 := by
      have heq : raw3765step0 = (fun i j => raw3765 (permutation35 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3765 permutation35 permutation10
    _ = injectiveMoment H node2082 := by rfl

def raw3766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3766step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical3766 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3766 = injectiveMoment H node1842 := by
  calc
    injectiveMoment H raw3766 = injectiveMoment H raw3766step0 := by
      have heq : raw3766step0 = (fun i j => raw3766 (permutation134 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3766 permutation134 permutation19
    _ = injectiveMoment H node1842 := by rfl

def raw3767 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw3767step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-2, 2, 0, 0]]

def raw3767step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3767 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3767 = injectiveMoment H node2015 := by
  calc
    injectiveMoment H raw3767 = injectiveMoment H raw3767step0 := by
      have heq : raw3767step0 = -raw3767 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3767).symm
    injectiveMoment H raw3767step0 = injectiveMoment H raw3767step1 := by
      have heq : raw3767step1 = (fun i j => raw3767step0 (permutation138 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3767step0 permutation138 permutation12
    _ = injectiveMoment H node2015 := by rfl

def raw3768 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3768step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3768step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical3768 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3768 = injectiveMoment H node2725 := by
  calc
    injectiveMoment H raw3768 = injectiveMoment H raw3768step0 := by
      have heq : raw3768step0 = -raw3768 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3768).symm
    injectiveMoment H raw3768step0 = injectiveMoment H raw3768step1 := by
      have heq : raw3768step1 = (fun i j => raw3768step0 (permutation44 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3768step0 permutation44 permutation30
    _ = injectiveMoment H node2725 := by rfl

def raw3769 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw3769step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3769 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3769 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw3769 = injectiveMoment H raw3769step0 := by
      have heq : raw3769step0 = (fun i j => raw3769 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3769 permutation29 permutation20
    _ = injectiveMoment H node1242 := by rfl

def raw3770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 1, -1, -1]]

def raw3770step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical3770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3770 = injectiveMoment H node1819 := by
  calc
    injectiveMoment H raw3770 = injectiveMoment H raw3770step0 := by
      have heq : raw3770step0 = (fun i j => raw3770 (permutation105 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3770 permutation105 permutation17
    _ = injectiveMoment H node1819 := by rfl

def raw3771 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw3771step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical3771 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3771 = injectiveMoment H node2073 := by
  calc
    injectiveMoment H raw3771 = injectiveMoment H raw3771step0 := by
      have heq : raw3771step0 = (fun i j => raw3771 (permutation144 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3771 permutation144 permutation25
    _ = injectiveMoment H node2073 := by rfl

def raw3772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3772step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3772 = injectiveMoment H node2632 := by
  calc
    injectiveMoment H raw3772 = injectiveMoment H raw3772step0 := by
      have heq : raw3772step0 = (fun i j => raw3772 (permutation124 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3772 permutation124 permutation18
    _ = injectiveMoment H node2632 := by rfl

def raw3773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3773step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3773 = injectiveMoment H node2744 := by
  calc
    injectiveMoment H raw3773 = injectiveMoment H raw3773step0 := by
      have heq : raw3773step0 = (fun i j => raw3773 (permutation124 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3773 permutation124 permutation18
    _ = injectiveMoment H node2744 := by rfl

def raw3774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3774step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 2, 0, -1], ![-1, 0, 1, 0]]

def raw3774step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3774 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3774 = injectiveMoment H node2065 := by
  calc
    injectiveMoment H raw3774 = injectiveMoment H raw3774step0 := by
      have heq : raw3774step0 = -raw3774 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3774).symm
    injectiveMoment H raw3774step0 = injectiveMoment H raw3774step1 := by
      have heq : raw3774step1 = (fun i j => raw3774step0 (permutation100 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3774step0 permutation100 permutation16
    _ = injectiveMoment H node2065 := by rfl

def raw3775 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3775step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical3775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3775 = injectiveMoment H node2085 := by
  calc
    injectiveMoment H raw3775 = injectiveMoment H raw3775step0 := by
      have heq : raw3775step0 = (fun i j => raw3775 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3775 permutation33 permutation10
    _ = injectiveMoment H node2085 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
