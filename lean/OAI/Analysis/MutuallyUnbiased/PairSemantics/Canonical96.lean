import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-2, 0, 0, 2]]

def raw3072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical3072 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3072 = injectiveMoment H node1296 := by
  calc
    injectiveMoment H raw3072 = injectiveMoment H raw3072step0 := by
      have heq : raw3072step0 = -raw3072 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3072).symm
    injectiveMoment H raw3072step0 = injectiveMoment H raw3072step1 := by
      have heq : raw3072step1 = (fun i j => raw3072step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3072step0 permutation25 permutation15
    _ = injectiveMoment H node1296 := by rfl

def raw3073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3073step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw3073step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical3073 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3073 = injectiveMoment H node2750 := by
  calc
    injectiveMoment H raw3073 = injectiveMoment H raw3073step0 := by
      have heq : raw3073step0 = -raw3073 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3073).symm
    injectiveMoment H raw3073step0 = injectiveMoment H raw3073step1 := by
      have heq : raw3073step1 = (fun i j => raw3073step0 (permutation102 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3073step0 permutation102 permutation15
    _ = injectiveMoment H node2750 := by rfl

def raw3074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3074step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![3, -1, -1, -1]]

def raw3074step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3074 = injectiveMoment H node946 := by
  calc
    injectiveMoment H raw3074 = injectiveMoment H raw3074step0 := by
      have heq : raw3074step0 = raw3074.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3074).symm
    injectiveMoment H raw3074step0 = injectiveMoment H raw3074step1 := by
      have heq : raw3074step1 = (fun i j => raw3074step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3074step0 permutation31 permutation26
    _ = injectiveMoment H node946 := by rfl

def raw3075 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw3075step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, -1, 2], ![-2, 0, 2, 0]]

def raw3075step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical3075 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3075 = injectiveMoment H node1235 := by
  calc
    injectiveMoment H raw3075 = injectiveMoment H raw3075step0 := by
      have heq : raw3075step0 = -raw3075 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3075).symm
    injectiveMoment H raw3075step0 = injectiveMoment H raw3075step1 := by
      have heq : raw3075step1 = (fun i j => raw3075step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3075step0 permutation25 permutation15
    _ = injectiveMoment H node1235 := by rfl

def raw3076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical3076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3076 = injectiveMoment H node1943 := by
  rfl

def raw3077 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical3077 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3077 = injectiveMoment H node1944 := by
  rfl

def raw3078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem canonical3078 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3078 = injectiveMoment H node588 := by
  rfl

def raw3079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3079step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3079 = injectiveMoment H node473 := by
  calc
    injectiveMoment H raw3079 = injectiveMoment H raw3079step0 := by
      have heq : raw3079step0 = (fun i j => raw3079 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3079 permutation11 permutation11
    _ = injectiveMoment H node473 := by rfl

def raw3080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw3080step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-1, 2, 1, -2], ![3, -1, -1, -1]]

def raw3080step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![1, -2, -1, 2], ![-3, 1, 1, 1]]

def raw3080step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

theorem canonical3080 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3080 = injectiveMoment H node505 := by
  calc
    injectiveMoment H raw3080 = injectiveMoment H raw3080step0 := by
      have heq : raw3080step0 = raw3080.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3080).symm
    injectiveMoment H raw3080step0 = injectiveMoment H raw3080step1 := by
      have heq : raw3080step1 = -raw3080step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3080step0).symm
    injectiveMoment H raw3080step1 = injectiveMoment H raw3080step2 := by
      have heq : raw3080step2 = (fun i j => raw3080step1 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3080step1 permutation22 permutation17
    _ = injectiveMoment H node505 := by rfl

def raw3081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw3081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical3081 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3081 = injectiveMoment H node1003 := by
  calc
    injectiveMoment H raw3081 = injectiveMoment H raw3081step0 := by
      have heq : raw3081step0 = -raw3081 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3081).symm
    injectiveMoment H raw3081step0 = injectiveMoment H raw3081step1 := by
      have heq : raw3081step1 = (fun i j => raw3081step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3081step0 permutation31 permutation15
    _ = injectiveMoment H node1003 := by rfl

def raw3082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-1, 2, 0, -1], ![3, -1, -1, -1]]

def raw3082step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical3082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3082 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw3082 = injectiveMoment H raw3082step0 := by
      have heq : raw3082step0 = raw3082.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3082).symm
    injectiveMoment H raw3082step0 = injectiveMoment H raw3082step1 := by
      have heq : raw3082step1 = (fun i j => raw3082step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3082step0 permutation30 permutation24
    _ = injectiveMoment H node939 := by rfl

def raw3083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw3083step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical3083 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3083 = injectiveMoment H node1007 := by
  calc
    injectiveMoment H raw3083 = injectiveMoment H raw3083step0 := by
      have heq : raw3083step0 = -raw3083 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3083).symm
    injectiveMoment H raw3083step0 = injectiveMoment H raw3083step1 := by
      have heq : raw3083step1 = (fun i j => raw3083step0 (permutation31 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3083step0 permutation31 permutation16
    _ = injectiveMoment H node1007 := by rfl

def raw3084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw3084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![-1, -1, 2, 0], ![-1, 0, -1, 2]]

def raw3084step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical3084 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3084 = injectiveMoment H node1007 := by
  calc
    injectiveMoment H raw3084 = injectiveMoment H raw3084step0 := by
      have heq : raw3084step0 = -raw3084 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3084).symm
    injectiveMoment H raw3084step0 = injectiveMoment H raw3084step1 := by
      have heq : raw3084step1 = (fun i j => raw3084step0 (permutation25 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3084step0 permutation25 permutation16
    _ = injectiveMoment H node1007 := by rfl

def raw3085 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 2, -2, -1], ![1, -1, 1, -1]]

def raw3085step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 2, -1], ![-1, 2, -2, 1], ![3, -1, -1, -1]]

def raw3085step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -2, 1], ![1, -2, 2, -1], ![-3, 1, 1, 1]]

def raw3085step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

theorem canonical3085 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3085 = injectiveMoment H node505 := by
  calc
    injectiveMoment H raw3085 = injectiveMoment H raw3085step0 := by
      have heq : raw3085step0 = raw3085.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3085).symm
    injectiveMoment H raw3085step0 = injectiveMoment H raw3085step1 := by
      have heq : raw3085step1 = -raw3085step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3085step0).symm
    injectiveMoment H raw3085step1 = injectiveMoment H raw3085step2 := by
      have heq : raw3085step2 = (fun i j => raw3085step1 (permutation22 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3085step1 permutation22 permutation19
    _ = injectiveMoment H node505 := by rfl

def raw3086 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical3086 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3086 = injectiveMoment H node1945 := by
  rfl

def raw3087 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![0, -1, 2, -1], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3087step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical3087 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3087 = injectiveMoment H node2826 := by
  calc
    injectiveMoment H raw3087 = injectiveMoment H raw3087step0 := by
      have heq : raw3087step0 = -raw3087 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3087).symm
    injectiveMoment H raw3087step0 = injectiveMoment H raw3087step1 := by
      have heq : raw3087step1 = (fun i j => raw3087step0 (permutation96 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3087step0 permutation96 permutation15
    _ = injectiveMoment H node2826 := by rfl

def raw3088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw3088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![0, -1, 2, -1], ![-2, 0, 0, 2]]

def raw3088step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical3088 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3088 = injectiveMoment H node1305 := by
  calc
    injectiveMoment H raw3088 = injectiveMoment H raw3088step0 := by
      have heq : raw3088step0 = -raw3088 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3088).symm
    injectiveMoment H raw3088step0 = injectiveMoment H raw3088step1 := by
      have heq : raw3088step1 = (fun i j => raw3088step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3088step0 permutation25 permutation15
    _ = injectiveMoment H node1305 := by rfl

def raw3089 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical3089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3089 = injectiveMoment H node1946 := by
  rfl

def raw3090 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical3090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3090 = injectiveMoment H node2698 := by
  calc
    injectiveMoment H raw3090 = injectiveMoment H raw3090step0 := by
      have heq : raw3090step0 = (fun i j => raw3090 (permutation62 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3090 permutation62 permutation16
    _ = injectiveMoment H node2698 := by rfl

def raw3091 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical3091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3091 = injectiveMoment H node1947 := by
  rfl

def raw3092 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical3092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3092 = injectiveMoment H node1948 := by
  rfl

def raw3093 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw3093step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 0, 0, 1]]

def raw3093step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical3093 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3093 = injectiveMoment H node2753 := by
  calc
    injectiveMoment H raw3093 = injectiveMoment H raw3093step0 := by
      have heq : raw3093step0 = -raw3093 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3093).symm
    injectiveMoment H raw3093step0 = injectiveMoment H raw3093step1 := by
      have heq : raw3093step1 = (fun i j => raw3093step0 (permutation102 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3093step0 permutation102 permutation15
    _ = injectiveMoment H node2753 := by rfl

def raw3094 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3094step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical3094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3094 = injectiveMoment H node2699 := by
  calc
    injectiveMoment H raw3094 = injectiveMoment H raw3094step0 := by
      have heq : raw3094step0 = (fun i j => raw3094 (permutation60 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3094 permutation60 permutation16
    _ = injectiveMoment H node2699 := by rfl

def raw3095 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical3095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3095 = injectiveMoment H node1949 := by
  rfl

def raw3096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem canonical3096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3096 = injectiveMoment H node589 := by
  rfl

def raw3097 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical3097 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3097 = injectiveMoment H node1950 := by
  rfl

def raw3098 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical3098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3098 = injectiveMoment H node1951 := by
  rfl

def raw3099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3099 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3099 = injectiveMoment H node590 := by
  rfl

def raw3100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw3100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, 1, 1, -1], ![-1, -2, 1, 2]]

def raw3100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

theorem canonical3100 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3100 = injectiveMoment H node519 := by
  calc
    injectiveMoment H raw3100 = injectiveMoment H raw3100step0 := by
      have heq : raw3100step0 = -raw3100 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3100).symm
    injectiveMoment H raw3100step0 = injectiveMoment H raw3100step1 := by
      have heq : raw3100step1 = (fun i j => raw3100step0 (permutation28 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3100step0 permutation28 permutation15
    _ = injectiveMoment H node519 := by rfl

def raw3101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw3101step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-1, 3, 0, -2], ![3, -2, 0, -1]]

def raw3101step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

theorem canonical3101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3101 = injectiveMoment H node990 := by
  calc
    injectiveMoment H raw3101 = injectiveMoment H raw3101step0 := by
      have heq : raw3101step0 = raw3101.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3101).symm
    injectiveMoment H raw3101step0 = injectiveMoment H raw3101step1 := by
      have heq : raw3101step1 = (fun i j => raw3101step0 (permutation20 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3101step0 permutation20 permutation23
    _ = injectiveMoment H node990 := by rfl

def raw3102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw3102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, 0, 2, -1], ![-1, -1, 0, 2]]

def raw3102step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical3102 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3102 = injectiveMoment H node1011 := by
  calc
    injectiveMoment H raw3102 = injectiveMoment H raw3102step0 := by
      have heq : raw3102step0 = -raw3102 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3102).symm
    injectiveMoment H raw3102step0 = injectiveMoment H raw3102step1 := by
      have heq : raw3102step1 = (fun i j => raw3102step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3102step0 permutation31 permutation15
    _ = injectiveMoment H node1011 := by rfl

def raw3103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3103step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-1, 3, -1, -1], ![3, -2, 0, -1]]

def raw3103step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical3103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3103 = injectiveMoment H node950 := by
  calc
    injectiveMoment H raw3103 = injectiveMoment H raw3103step0 := by
      have heq : raw3103step0 = raw3103.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3103).symm
    injectiveMoment H raw3103step0 = injectiveMoment H raw3103step1 := by
      have heq : raw3103step1 = (fun i j => raw3103step0 (permutation26 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3103step0 permutation26 permutation25
    _ = injectiveMoment H node950 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
