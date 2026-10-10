import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3936 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]

def raw3936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw3936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical3936 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3936 = injectiveMoment H node654 := by
  calc
    injectiveMoment H raw3936 = injectiveMoment H raw3936step0 := by
      have heq : raw3936step0 = -raw3936 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3936).symm
    injectiveMoment H raw3936step0 = injectiveMoment H raw3936step1 := by
      have heq : raw3936step1 = (fun i j => raw3936step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3936step0 permutation33 permutation8
    _ = injectiveMoment H node654 := by rfl

def raw3937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]

def raw3937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

theorem canonical3937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3937 = injectiveMoment H node2103 := by
  calc
    injectiveMoment H raw3937 = injectiveMoment H raw3937step0 := by
      have heq : raw3937step0 = (fun i j => raw3937 (permutation370 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3937 permutation370 permutation8
    _ = injectiveMoment H node2103 := by rfl

def raw3938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]

def raw3938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]

def raw3938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical3938 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3938 = injectiveMoment H node2104 := by
  calc
    injectiveMoment H raw3938 = injectiveMoment H raw3938step0 := by
      have heq : raw3938step0 = -raw3938 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3938).symm
    injectiveMoment H raw3938step0 = injectiveMoment H raw3938step1 := by
      have heq : raw3938step1 = (fun i j => raw3938step0 (permutation176 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3938step0 permutation176 permutation8
    _ = injectiveMoment H node2104 := by rfl

def raw3939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]

def raw3939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw3939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3939 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3939 = injectiveMoment H node2136 := by
  calc
    injectiveMoment H raw3939 = injectiveMoment H raw3939step0 := by
      have heq : raw3939step0 = -raw3939 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3939).symm
    injectiveMoment H raw3939step0 = injectiveMoment H raw3939step1 := by
      have heq : raw3939step1 = (fun i j => raw3939step0 (permutation158 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3939step0 permutation158 permutation8
    _ = injectiveMoment H node2136 := by rfl

def raw3940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw3940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw3940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem canonical3940 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3940 = injectiveMoment H node1529 := by
  calc
    injectiveMoment H raw3940 = injectiveMoment H raw3940step0 := by
      have heq : raw3940step0 = -raw3940 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3940).symm
    injectiveMoment H raw3940step0 = injectiveMoment H raw3940step1 := by
      have heq : raw3940step1 = (fun i j => raw3940step0 (permutation405 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3940step0 permutation405 permutation3
    _ = injectiveMoment H node1529 := by rfl

def raw3941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw3941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3941 = injectiveMoment H node2795 := by
  calc
    injectiveMoment H raw3941 = injectiveMoment H raw3941step0 := by
      have heq : raw3941step0 = (fun i j => raw3941 (permutation233 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3941 permutation233 permutation5
    _ = injectiveMoment H node2795 := by rfl

def raw3942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw3942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3942 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3942 = injectiveMoment H node2666 := by
  calc
    injectiveMoment H raw3942 = injectiveMoment H raw3942step0 := by
      have heq : raw3942step0 = (fun i j => raw3942 (permutation369 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3942 permutation369 permutation6
    _ = injectiveMoment H node2666 := by rfl

def raw3943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

theorem canonical3943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3943 = injectiveMoment H node2097 := by
  rfl

def raw3944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical3944 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3944 = injectiveMoment H node2098 := by
  rfl

def raw3945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw3945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical3945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3945 = injectiveMoment H node2798 := by
  calc
    injectiveMoment H raw3945 = injectiveMoment H raw3945step0 := by
      have heq : raw3945step0 = (fun i j => raw3945 (permutation226 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3945 permutation226 permutation5
    _ = injectiveMoment H node2798 := by rfl

def raw3946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical3946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3946 = injectiveMoment H node1142 := by
  calc
    injectiveMoment H raw3946 = injectiveMoment H raw3946step0 := by
      have heq : raw3946step0 = (fun i j => raw3946 (permutation140 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3946 permutation140 permutation6
    _ = injectiveMoment H node1142 := by rfl

def raw3947 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3947step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical3947 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3947 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw3947 = injectiveMoment H raw3947step0 := by
      have hz : ∀ j, raw3947 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3947step0 = (fun i j => raw3947 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3947 permutation80 hz
    injectiveMoment H raw3947step0 = injectiveMoment H raw3947step1 := by
      have heq : raw3947step1 = (fun i j => raw3947step0 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3947step0 permutation31 permutation6
    _ = injectiveMoment H node284 := by rfl

def raw3948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical3948 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3948 = injectiveMoment H node2099 := by
  rfl

def raw3949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3949 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3949 = injectiveMoment H node2100 := by
  rfl

def raw3950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw3950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3950 = injectiveMoment H node2301 := by
  calc
    injectiveMoment H raw3950 = injectiveMoment H raw3950step0 := by
      have heq : raw3950step0 = (fun i j => raw3950 (permutation245 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3950 permutation245 permutation5
    _ = injectiveMoment H node2301 := by rfl

def raw3951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3951 = injectiveMoment H node706 := by
  calc
    injectiveMoment H raw3951 = injectiveMoment H raw3951step0 := by
      have heq : raw3951step0 = (fun i j => raw3951 (permutation108 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3951 permutation108 permutation5
    _ = injectiveMoment H node706 := by rfl

def raw3952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw3952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-2, -1, 3]]

def raw3952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical3952 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3952 = injectiveMoment H node1859 := by
  calc
    injectiveMoment H raw3952 = injectiveMoment H raw3952step0 := by
      have heq : raw3952step0 = -raw3952 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3952).symm
    injectiveMoment H raw3952step0 = injectiveMoment H raw3952step1 := by
      have heq : raw3952step1 = (fun i j => raw3952step0 (permutation388 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3952step0 permutation388 permutation3
    _ = injectiveMoment H node1859 := by rfl

def raw3953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw3953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw3953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3953 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3953 = injectiveMoment H node2137 := by
  calc
    injectiveMoment H raw3953 = injectiveMoment H raw3953step0 := by
      have heq : raw3953step0 = -raw3953 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3953).symm
    injectiveMoment H raw3953step0 = injectiveMoment H raw3953step1 := by
      have heq : raw3953step1 = (fun i j => raw3953step0 (permutation158 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3953step0 permutation158 permutation8
    _ = injectiveMoment H node2137 := by rfl

def raw3954 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw3954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw3954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3954 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3954 = injectiveMoment H node659 := by
  calc
    injectiveMoment H raw3954 = injectiveMoment H raw3954step0 := by
      have heq : raw3954step0 = -raw3954 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3954).symm
    injectiveMoment H raw3954step0 = injectiveMoment H raw3954step1 := by
      have heq : raw3954step1 = (fun i j => raw3954step0 (permutation35 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3954step0 permutation35 permutation8
    _ = injectiveMoment H node659 := by rfl

def raw3955 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3955 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3955 = injectiveMoment H node661 := by
  calc
    injectiveMoment H raw3955 = injectiveMoment H raw3955step0 := by
      have heq : raw3955step0 = (fun i j => raw3955 (permutation146 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3955 permutation146 permutation6
    _ = injectiveMoment H node661 := by rfl

def raw3956 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical3956 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3956 = injectiveMoment H node624 := by
  rfl

def raw3957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw3957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical3957 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3957 = injectiveMoment H node2135 := by
  calc
    injectiveMoment H raw3957 = injectiveMoment H raw3957step0 := by
      have heq : raw3957step0 = (fun i j => raw3957 (permutation227 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3957 permutation227 permutation7
    _ = injectiveMoment H node2135 := by rfl

def raw3958 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw3958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical3958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3958 = injectiveMoment H node656 := by
  calc
    injectiveMoment H raw3958 = injectiveMoment H raw3958step0 := by
      have heq : raw3958step0 = (fun i j => raw3958 (permutation89 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3958 permutation89 permutation7
    _ = injectiveMoment H node656 := by rfl

def raw3959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw3959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3959 = injectiveMoment H node705 := by
  calc
    injectiveMoment H raw3959 = injectiveMoment H raw3959step0 := by
      have heq : raw3959step0 = (fun i j => raw3959 (permutation82 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3959 permutation82 permutation5
    _ = injectiveMoment H node705 := by rfl

def raw3960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw3960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw3960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical3960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3960 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw3960 = injectiveMoment H raw3960step0 := by
      have heq : raw3960step0 = -raw3960 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3960).symm
    injectiveMoment H raw3960step0 = injectiveMoment H raw3960step1 := by
      have heq : raw3960step1 = (fun i j => raw3960step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3960step0 permutation33 permutation8
    _ = injectiveMoment H node655 := by rfl

def raw3961 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw3961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw3961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical3961 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3961 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H raw3961 = injectiveMoment H raw3961step0 := by
      have heq : raw3961step0 = -raw3961 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3961).symm
    injectiveMoment H raw3961step0 = injectiveMoment H raw3961step1 := by
      have heq : raw3961step1 = (fun i j => raw3961step0 (permutation60 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3961step0 permutation60 permutation6
    _ = injectiveMoment H node1291 := by rfl

def raw3962 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3962step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical3962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3962 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw3962 = injectiveMoment H raw3962step0 := by
      have heq : raw3962step0 = (fun i j => raw3962 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3962 permutation25 permutation6
    _ = injectiveMoment H node291 := by rfl

def raw3963 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw3963step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw3963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical3963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3963 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw3963 = injectiveMoment H raw3963step0 := by
      have heq : raw3963step0 = -raw3963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3963).symm
    injectiveMoment H raw3963step0 = injectiveMoment H raw3963step1 := by
      have heq : raw3963step1 = (fun i j => raw3963step0 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3963step0 permutation10 permutation8
    _ = injectiveMoment H node203 := by rfl

def raw3964 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def raw3964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical3964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3964 = injectiveMoment H node642 := by
  calc
    injectiveMoment H raw3964 = injectiveMoment H raw3964step0 := by
      have heq : raw3964step0 = (fun i j => raw3964 (permutation83 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3964 permutation83 permutation5
    _ = injectiveMoment H node642 := by rfl

def raw3965 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical3965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3965 = injectiveMoment H node625 := by
  rfl

def raw3966 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]

def raw3966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]

def raw3966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3966 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3966 = injectiveMoment H node705 := by
  calc
    injectiveMoment H raw3966 = injectiveMoment H raw3966step0 := by
      have heq : raw3966step0 = -raw3966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3966).symm
    injectiveMoment H raw3966step0 = injectiveMoment H raw3966step1 := by
      have heq : raw3966step1 = (fun i j => raw3966step0 (permutation59 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3966step0 permutation59 permutation6
    _ = injectiveMoment H node705 := by rfl

def raw3967 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]

def raw3967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical3967 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3967 = injectiveMoment H node624 := by
  calc
    injectiveMoment H raw3967 = injectiveMoment H raw3967step0 := by
      have heq : raw3967step0 = (fun i j => raw3967 (permutation140 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3967 permutation140 permutation6
    _ = injectiveMoment H node624 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
