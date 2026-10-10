import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, -1, 0, 0]]

def raw3808step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 0, -1, 2], ![-1, 1, 0, 0]]

def raw3808step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3808 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw3808 = injectiveMoment H raw3808step0 := by
      have heq : raw3808step0 = -raw3808 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3808).symm
    injectiveMoment H raw3808step0 = injectiveMoment H raw3808step1 := by
      have heq : raw3808step1 = (fun i j => raw3808step0 (permutation15 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3808step0 permutation15 permutation19
    _ = injectiveMoment H node1009 := by rfl

def raw3809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3809step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3809 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3809 = injectiveMoment H node2744 := by
  calc
    injectiveMoment H raw3809 = injectiveMoment H raw3809step0 := by
      have heq : raw3809step0 = (fun i j => raw3809 (permutation126 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3809 permutation126 permutation20
    _ = injectiveMoment H node2744 := by rfl

def raw3810 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3810step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3810 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3810 = injectiveMoment H node2632 := by
  calc
    injectiveMoment H raw3810 = injectiveMoment H raw3810step0 := by
      have heq : raw3810step0 = (fun i j => raw3810 (permutation126 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3810 permutation126 permutation20
    _ = injectiveMoment H node2632 := by rfl

def raw3811 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3811step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3811 = injectiveMoment H node1117 := by
  calc
    injectiveMoment H raw3811 = injectiveMoment H raw3811step0 := by
      have hz : ∀ j, raw3811 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3811step0 = (fun i j => raw3811 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3811 permutation80 hz
    injectiveMoment H raw3811step0 = injectiveMoment H raw3811step1 := by
      have heq : raw3811step1 = (fun i j => raw3811step0 (permutation26 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3811step0 permutation26 permutation30
    _ = injectiveMoment H node1117 := by rfl

def raw3812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3812step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3812step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical3812 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3812 = injectiveMoment H node2725 := by
  calc
    injectiveMoment H raw3812 = injectiveMoment H raw3812step0 := by
      have heq : raw3812step0 = -raw3812 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3812).symm
    injectiveMoment H raw3812step0 = injectiveMoment H raw3812step1 := by
      have heq : raw3812step1 = (fun i j => raw3812step0 (permutation38 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3812step0 permutation38 permutation30
    _ = injectiveMoment H node2725 := by rfl

def raw3813 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 1, -2]]

def raw3813step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical3813 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3813 = injectiveMoment H node2087 := by
  calc
    injectiveMoment H raw3813 = injectiveMoment H raw3813step0 := by
      have heq : raw3813step0 = (fun i j => raw3813 (permutation108 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3813 permutation108 permutation17
    _ = injectiveMoment H node2087 := by rfl

def raw3814 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3814step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, 0, 0, 1]]

def raw3814step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical3814 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3814 = injectiveMoment H node2587 := by
  calc
    injectiveMoment H raw3814 = injectiveMoment H raw3814step0 := by
      have heq : raw3814step0 = -raw3814 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3814).symm
    injectiveMoment H raw3814step0 = injectiveMoment H raw3814step1 := by
      have heq : raw3814step1 = (fun i j => raw3814step0 (permutation45 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3814step0 permutation45 permutation32
    _ = injectiveMoment H node2587 := by rfl

def raw3815 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3815step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, -1, 1]]

def raw3815step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical3815 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3815 = injectiveMoment H node2612 := by
  calc
    injectiveMoment H raw3815 = injectiveMoment H raw3815step0 := by
      have heq : raw3815step0 = -raw3815 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3815).symm
    injectiveMoment H raw3815step0 = injectiveMoment H raw3815step1 := by
      have heq : raw3815step1 = (fun i j => raw3815step0 (permutation45 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3815step0 permutation45 permutation32
    _ = injectiveMoment H node2612 := by rfl

def raw3816 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3816step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 1, 0, 0]]

def raw3816step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical3816 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3816 = injectiveMoment H node2612 := by
  calc
    injectiveMoment H raw3816 = injectiveMoment H raw3816step0 := by
      have heq : raw3816step0 = -raw3816 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3816).symm
    injectiveMoment H raw3816step0 = injectiveMoment H raw3816step1 := by
      have heq : raw3816step1 = (fun i j => raw3816step0 (permutation51 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3816step0 permutation51 permutation32
    _ = injectiveMoment H node2612 := by rfl

def raw3817 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3817step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![-1, 0, 1, 0]]

def raw3817step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical3817 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3817 = injectiveMoment H node2588 := by
  calc
    injectiveMoment H raw3817 = injectiveMoment H raw3817step0 := by
      have heq : raw3817step0 = -raw3817 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3817).symm
    injectiveMoment H raw3817step0 = injectiveMoment H raw3817step1 := by
      have heq : raw3817step1 = (fun i j => raw3817step0 (permutation46 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3817step0 permutation46 permutation32
    _ = injectiveMoment H node2588 := by rfl

def raw3818 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical3818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3818 = injectiveMoment H node2088 := by
  rfl

def raw3819 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3819step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3819step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical3819 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3819 = injectiveMoment H node2607 := by
  calc
    injectiveMoment H raw3819 = injectiveMoment H raw3819step0 := by
      have heq : raw3819step0 = -raw3819 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3819).symm
    injectiveMoment H raw3819step0 = injectiveMoment H raw3819step1 := by
      have heq : raw3819step1 = (fun i j => raw3819step0 (permutation50 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3819step0 permutation50 permutation26
    _ = injectiveMoment H node2607 := by rfl

def raw3820 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

def raw3820step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical3820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3820 = injectiveMoment H node2088 := by
  calc
    injectiveMoment H raw3820 = injectiveMoment H raw3820step0 := by
      have heq : raw3820step0 = (fun i j => raw3820 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3820 permutation34 permutation9
    _ = injectiveMoment H node2088 := by rfl

def raw3821 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3821step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical3821 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3821 = injectiveMoment H node2073 := by
  calc
    injectiveMoment H raw3821 = injectiveMoment H raw3821step0 := by
      have heq : raw3821step0 = (fun i j => raw3821 (permutation122 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3821 permutation122 permutation18
    _ = injectiveMoment H node2073 := by rfl

def raw3822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3822step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical3822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3822 = injectiveMoment H node2084 := by
  calc
    injectiveMoment H raw3822 = injectiveMoment H raw3822step0 := by
      have heq : raw3822step0 = (fun i j => raw3822 (permutation90 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3822 permutation90 permutation28
    _ = injectiveMoment H node2084 := by rfl

def raw3823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3823step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical3823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3823 = injectiveMoment H node2084 := by
  calc
    injectiveMoment H raw3823 = injectiveMoment H raw3823step0 := by
      have heq : raw3823step0 = (fun i j => raw3823 (permutation88 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3823 permutation88 permutation28
    _ = injectiveMoment H node2084 := by rfl

def raw3824 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw3824step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3824step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw3824step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3824 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3824 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw3824 = injectiveMoment H raw3824step0 := by
      have heq : raw3824step0 = raw3824.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3824).symm
    injectiveMoment H raw3824step0 = injectiveMoment H raw3824step1 := by
      have heq : raw3824step1 = -raw3824step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3824step0).symm
    injectiveMoment H raw3824step1 = injectiveMoment H raw3824step2 := by
      have heq : raw3824step2 = (fun i j => raw3824step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3824step1 permutation16 permutation17
    _ = injectiveMoment H node1058 := by rfl

def raw3825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw3825step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -3, 2]]

def raw3825step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, -2, 2], ![-1, 0, 3, -2]]

def raw3825step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3825 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3825 = injectiveMoment H node1250 := by
  calc
    injectiveMoment H raw3825 = injectiveMoment H raw3825step0 := by
      have heq : raw3825step0 = raw3825.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3825).symm
    injectiveMoment H raw3825step0 = injectiveMoment H raw3825step1 := by
      have heq : raw3825step1 = -raw3825step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3825step0).symm
    injectiveMoment H raw3825step1 = injectiveMoment H raw3825step2 := by
      have heq : raw3825step2 = (fun i j => raw3825step1 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3825step1 permutation19 permutation15
    _ = injectiveMoment H node1250 := by rfl

def raw3826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, -2, 3], ![1, 1, 2, -4]]

def raw3826step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, -2, 2], ![1, 0, 3, -4]]

def raw3826step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, 2, -2], ![-1, 0, -3, 4]]

def raw3826step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

theorem canonical3826 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3826 = injectiveMoment H node1251 := by
  calc
    injectiveMoment H raw3826 = injectiveMoment H raw3826step0 := by
      have heq : raw3826step0 = raw3826.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3826).symm
    injectiveMoment H raw3826step0 = injectiveMoment H raw3826step1 := by
      have heq : raw3826step1 = -raw3826step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3826step0).symm
    injectiveMoment H raw3826step1 = injectiveMoment H raw3826step2 := by
      have heq : raw3826step2 = (fun i j => raw3826step1 (permutation19 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3826step1 permutation19 permutation16
    _ = injectiveMoment H node1251 := by rfl

def raw3827 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 1, -3]]

def raw3827step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3827step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw3827step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3827 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3827 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw3827 = injectiveMoment H raw3827step0 := by
      have heq : raw3827step0 = raw3827.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3827).symm
    injectiveMoment H raw3827step0 = injectiveMoment H raw3827step1 := by
      have heq : raw3827step1 = -raw3827step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3827step0).symm
    injectiveMoment H raw3827step1 = injectiveMoment H raw3827step2 := by
      have heq : raw3827step2 = (fun i j => raw3827step1 (permutation19 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3827step1 permutation19 permutation16
    _ = injectiveMoment H node1249 := by rfl

def raw3828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3828step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, -1, 1, 1]]

def raw3828step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical3828 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3828 = injectiveMoment H node1006 := by
  calc
    injectiveMoment H raw3828 = injectiveMoment H raw3828step0 := by
      have heq : raw3828step0 = -raw3828 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3828).symm
    injectiveMoment H raw3828step0 = injectiveMoment H raw3828step1 := by
      have heq : raw3828step1 = (fun i j => raw3828step0 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3828step0 permutation11 permutation32
    _ = injectiveMoment H node1006 := by rfl

def raw3829 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw3829step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical3829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3829 = injectiveMoment H node1126 := by
  calc
    injectiveMoment H raw3829 = injectiveMoment H raw3829step0 := by
      have heq : raw3829step0 = (fun i j => raw3829 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3829 permutation22 permutation17
    _ = injectiveMoment H node1126 := by rfl

def raw3830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3830step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3830 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3830 = injectiveMoment H node1117 := by
  calc
    injectiveMoment H raw3830 = injectiveMoment H raw3830step0 := by
      have heq : raw3830step0 = (fun i j => raw3830 (permutation26 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3830 permutation26 permutation30
    _ = injectiveMoment H node1117 := by rfl

def raw3831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw3831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![-1, 2, 0, -1], ![-1, -1, 1, 1]]

def raw3831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical3831 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3831 = injectiveMoment H node1006 := by
  calc
    injectiveMoment H raw3831 = injectiveMoment H raw3831step0 := by
      have heq : raw3831step0 = -raw3831 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3831).symm
    injectiveMoment H raw3831step0 = injectiveMoment H raw3831step1 := by
      have heq : raw3831step1 = (fun i j => raw3831step0 (permutation11 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3831step0 permutation11 permutation26
    _ = injectiveMoment H node1006 := by rfl

def raw3832 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3832step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![-1, -1, 2, 0]]

def raw3832step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3832 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3832 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw3832 = injectiveMoment H raw3832step0 := by
      have heq : raw3832step0 = -raw3832 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3832).symm
    injectiveMoment H raw3832step0 = injectiveMoment H raw3832step1 := by
      have heq : raw3832step1 = (fun i j => raw3832step0 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3832step0 permutation12 permutation32
    _ = injectiveMoment H node1009 := by rfl

def raw3833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3833step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3833 = injectiveMoment H node1117 := by
  calc
    injectiveMoment H raw3833 = injectiveMoment H raw3833step0 := by
      have heq : raw3833step0 = (fun i j => raw3833 (permutation26 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3833 permutation26 permutation24
    _ = injectiveMoment H node1117 := by rfl

def raw3834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical3834 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3834 = injectiveMoment H node1126 := by
  calc
    injectiveMoment H raw3834 = injectiveMoment H raw3834step0 := by
      have heq : raw3834step0 = (fun i j => raw3834 (permutation22 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3834 permutation22 permutation19
    _ = injectiveMoment H node1126 := by rfl

def raw3835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw3835step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical3835 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3835 = injectiveMoment H node1126 := by
  calc
    injectiveMoment H raw3835 = injectiveMoment H raw3835step0 := by
      have heq : raw3835step0 = (fun i j => raw3835 (permutation28 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3835 permutation28 permutation19
    _ = injectiveMoment H node1126 := by rfl

def raw3836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw3836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

theorem canonical3836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3836 = injectiveMoment H node620 := by
  calc
    injectiveMoment H raw3836 = injectiveMoment H raw3836step0 := by
      have heq : raw3836step0 = (fun i j => raw3836 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3836 permutation9 permutation10
    _ = injectiveMoment H node620 := by rfl

def raw3837 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -3, 1]]

def raw3837step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

theorem canonical3837 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3837 = injectiveMoment H node619 := by
  calc
    injectiveMoment H raw3837 = injectiveMoment H raw3837step0 := by
      have heq : raw3837step0 = (fun i j => raw3837 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3837 permutation9 permutation10
    _ = injectiveMoment H node619 := by rfl

def raw3838 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3838step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3838step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical3838 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3838 = injectiveMoment H node1006 := by
  calc
    injectiveMoment H raw3838 = injectiveMoment H raw3838step0 := by
      have heq : raw3838step0 = -raw3838 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3838).symm
    injectiveMoment H raw3838step0 = injectiveMoment H raw3838step1 := by
      have heq : raw3838step1 = (fun i j => raw3838step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3838step0 permutation16 permutation17
    _ = injectiveMoment H node1006 := by rfl

def raw3839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw3839step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3839 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3839 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw3839 = injectiveMoment H raw3839step0 := by
      have heq : raw3839step0 = -raw3839 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3839).symm
    injectiveMoment H raw3839step0 = injectiveMoment H raw3839step1 := by
      have heq : raw3839step1 = (fun i j => raw3839step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3839step0 permutation16 permutation17
    _ = injectiveMoment H node1009 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
