import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6912 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 4, -1, -2], ![2, -3, -1, 2]]

def raw6912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![2, -1, -1], ![0, -2, 2]]

def raw6912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -4, 3], ![-2, 1, 1], ![0, 2, -2]]

def raw6912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical6912 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6912 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw6912 = injectiveMoment H raw6912step0 := by
      have heq : raw6912step0 = raw6912.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6912).symm
    injectiveMoment H raw6912step0 = injectiveMoment H raw6912step1 := by
      have heq : raw6912step1 = -raw6912step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6912step0).symm
    injectiveMoment H raw6912step1 = injectiveMoment H raw6912step2 := by
      have heq : raw6912step2 = (fun i j => raw6912step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6912step1 permutation25 permutation4
    _ = injectiveMoment H node225 := by rfl

def raw6913 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -3, 1, 2], ![1, 4, -3, -2]]

def raw6913step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![2, 1, -3], ![0, 2, -2]]

def raw6913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 3, -4], ![-2, -1, 3], ![0, -2, 2]]

def raw6913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

theorem canonical6913 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6913 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw6913 = injectiveMoment H raw6913step0 := by
      have heq : raw6913step0 = raw6913.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6913).symm
    injectiveMoment H raw6913step0 = injectiveMoment H raw6913step1 := by
      have heq : raw6913step1 = -raw6913step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6913step0).symm
    injectiveMoment H raw6913step1 = injectiveMoment H raw6913step2 := by
      have heq : raw6913step2 = (fun i j => raw6913step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6913step1 permutation25 permutation3
    _ = injectiveMoment H node166 := by rfl

def raw6914 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, -1, 3], ![1, 3, -1, -3]]

def raw6914step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![2, -1, -1], ![0, 3, -3]]

def raw6914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 2, -3], ![-2, 1, 1], ![0, -3, 3]]

def raw6914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical6914 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6914 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw6914 = injectiveMoment H raw6914step0 := by
      have heq : raw6914step0 = raw6914.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6914).symm
    injectiveMoment H raw6914step0 = injectiveMoment H raw6914step1 := by
      have heq : raw6914step1 = -raw6914step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6914step0).symm
    injectiveMoment H raw6914step1 = injectiveMoment H raw6914step2 := by
      have heq : raw6914step2 = (fun i j => raw6914step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6914step1 permutation25 permutation3
    _ = injectiveMoment H node222 := by rfl

def raw6915 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, 1, 1], ![1, 3, -3, -1]]

def raw6915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![2, 1, -3], ![0, 1, -1]]

def raw6915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical6915 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6915 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw6915 = injectiveMoment H raw6915step0 := by
      have heq : raw6915step0 = raw6915.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6915).symm
    injectiveMoment H raw6915step0 = injectiveMoment H raw6915step1 := by
      have heq : raw6915step1 = (fun i j => raw6915step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6915step0 permutation16 permutation5
    _ = injectiveMoment H node174 := by rfl

def raw6916 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw6916step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -2, 0], ![0, 1, 3, -4], ![0, -1, -1, 2], ![-1, -1, 0, 2]]

def raw6916step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical6916 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6916 = injectiveMoment H node996 := by
  calc
    injectiveMoment H raw6916 = injectiveMoment H raw6916step0 := by
      have heq : raw6916step0 = -raw6916 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6916).symm
    injectiveMoment H raw6916step0 = injectiveMoment H raw6916step1 := by
      have heq : raw6916step1 = (fun i j => raw6916step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6916step0 permutation32 permutation9
    _ = injectiveMoment H node996 := by rfl

def raw6917 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![1, 2, 1, -4]]

def raw6917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, -3, 1], ![0, 4, -4]]

def raw6917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, 3, -1], ![0, -4, 4]]

def raw6917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical6917 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6917 = injectiveMoment H node190 := by
  calc
    injectiveMoment H raw6917 = injectiveMoment H raw6917step0 := by
      have heq : raw6917step0 = raw6917.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6917).symm
    injectiveMoment H raw6917step0 = injectiveMoment H raw6917step1 := by
      have heq : raw6917step1 = -raw6917step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6917step0).symm
    injectiveMoment H raw6917step1 = injectiveMoment H raw6917step2 := by
      have heq : raw6917step2 = (fun i j => raw6917step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6917step1 permutation26 permutation4
    _ = injectiveMoment H node190 := by rfl

def raw6918 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6918step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![2, -2, 0, 0], ![0, 3, -1, -2]]

def raw6918step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical6918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6918 = injectiveMoment H node805 := by
  calc
    injectiveMoment H raw6918 = injectiveMoment H raw6918step0 := by
      have heq : raw6918step0 = raw6918.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6918).symm
    injectiveMoment H raw6918step0 = injectiveMoment H raw6918step1 := by
      have heq : raw6918step1 = (fun i j => raw6918step0 (permutation31 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6918step0 permutation31 permutation25
    _ = injectiveMoment H node805 := by rfl

def raw6919 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6919step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![2, -2, 0, 0], ![0, 3, -2, -1]]

def raw6919step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical6919 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6919 = injectiveMoment H node807 := by
  calc
    injectiveMoment H raw6919 = injectiveMoment H raw6919step0 := by
      have heq : raw6919step0 = raw6919.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6919).symm
    injectiveMoment H raw6919step0 = injectiveMoment H raw6919step1 := by
      have heq : raw6919step1 = (fun i j => raw6919step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6919step0 permutation32 permutation31
    _ = injectiveMoment H node807 := by rfl

def raw6920 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![1, 2, 0, -3]]

def raw6920step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, -2, 0], ![0, 3, -3]]

def raw6920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, 2, 0], ![0, -3, 3]]

def raw6920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical6920 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6920 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw6920 = injectiveMoment H raw6920step0 := by
      have heq : raw6920step0 = raw6920.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6920).symm
    injectiveMoment H raw6920step0 = injectiveMoment H raw6920step1 := by
      have heq : raw6920step1 = -raw6920step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6920step0).symm
    injectiveMoment H raw6920step1 = injectiveMoment H raw6920step2 := by
      have heq : raw6920step2 = (fun i j => raw6920step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6920step1 permutation26 permutation4
    _ = injectiveMoment H node215 := by rfl

def raw6921 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6921step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical6921 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6921 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw6921 = injectiveMoment H raw6921step0 := by
      have heq : raw6921step0 = (fun i j => raw6921 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6921 permutation9 permutation10
    _ = injectiveMoment H node1009 := by rfl

def raw6922 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw6922step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

theorem canonical6922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6922 = injectiveMoment H node1001 := by
  calc
    injectiveMoment H raw6922 = injectiveMoment H raw6922step0 := by
      have heq : raw6922step0 = (fun i j => raw6922 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6922 permutation9 permutation10
    _ = injectiveMoment H node1001 := by rfl

def raw6923 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, 2, -1], ![1, 2, -4, 1]]

def raw6923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, 2, -4], ![0, -1, 1]]

def raw6923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, -2, 4], ![0, 1, -1]]

def raw6923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6923 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6923 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw6923 = injectiveMoment H raw6923step0 := by
      have heq : raw6923step0 = raw6923.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6923).symm
    injectiveMoment H raw6923step0 = injectiveMoment H raw6923step1 := by
      have heq : raw6923step1 = -raw6923step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6923step0).symm
    injectiveMoment H raw6923step1 = injectiveMoment H raw6923step2 := by
      have heq : raw6923step2 = (fun i j => raw6923step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6923step1 permutation25 permutation3
    _ = injectiveMoment H node150 := by rfl

def raw6924 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, 3, -2], ![1, 2, -5, 2]]

def raw6924step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, 3, -5], ![0, -2, 2]]

def raw6924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, -3, 5], ![0, 2, -2]]

def raw6924step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6924 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6924 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw6924 = injectiveMoment H raw6924step0 := by
      have heq : raw6924step0 = raw6924.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6924).symm
    injectiveMoment H raw6924step0 = injectiveMoment H raw6924step1 := by
      have heq : raw6924step1 = -raw6924step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6924step0).symm
    injectiveMoment H raw6924step1 = injectiveMoment H raw6924step2 := by
      have heq : raw6924step2 = (fun i j => raw6924step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6924step1 permutation25 permutation3
    _ = injectiveMoment H node127 := by rfl

def raw6925 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6925step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem canonical6925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6925 = injectiveMoment H node1065 := by
  calc
    injectiveMoment H raw6925 = injectiveMoment H raw6925step0 := by
      have heq : raw6925step0 = (fun i j => raw6925 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6925 permutation9 permutation10
    _ = injectiveMoment H node1065 := by rfl

def raw6926 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6926step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical6926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6926 = injectiveMoment H node1054 := by
  calc
    injectiveMoment H raw6926 = injectiveMoment H raw6926step0 := by
      have heq : raw6926step0 = (fun i j => raw6926 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6926 permutation9 permutation10
    _ = injectiveMoment H node1054 := by rfl

def raw6927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6927step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical6927 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6927 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw6927 = injectiveMoment H raw6927step0 := by
      have heq : raw6927step0 = (fun i j => raw6927 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6927 permutation9 permutation10
    _ = injectiveMoment H node1057 := by rfl

def raw6928 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def raw6928step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![0, 2, -2]]

def raw6928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical6928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6928 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw6928 = injectiveMoment H raw6928step0 := by
      have heq : raw6928step0 = raw6928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6928).symm
    injectiveMoment H raw6928step0 = injectiveMoment H raw6928step1 := by
      have heq : raw6928step1 = (fun i j => raw6928step0 (permutation21 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6928step0 permutation21 permutation6
    _ = injectiveMoment H node207 := by rfl

def raw6929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw6929step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![2, -1, 0, -1], ![0, 1, -2, 1]]

def raw6929step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![0, -1, 2, -1]]

def raw6929step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical6929 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6929 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw6929 = injectiveMoment H raw6929step0 := by
      have heq : raw6929step0 = raw6929.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6929).symm
    injectiveMoment H raw6929step0 = injectiveMoment H raw6929step1 := by
      have heq : raw6929step1 = -raw6929step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6929step0).symm
    injectiveMoment H raw6929step1 = injectiveMoment H raw6929step2 := by
      have heq : raw6929step2 = (fun i j => raw6929step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6929step1 permutation27 permutation19
    _ = injectiveMoment H node1000 := by rfl

def raw6930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw6930step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

theorem canonical6930 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6930 = injectiveMoment H node1049 := by
  calc
    injectiveMoment H raw6930 = injectiveMoment H raw6930step0 := by
      have heq : raw6930step0 = (fun i j => raw6930 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6930 permutation9 permutation10
    _ = injectiveMoment H node1049 := by rfl

def raw6931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw6931step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw6931step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical6931 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6931 = injectiveMoment H node799 := by
  calc
    injectiveMoment H raw6931 = injectiveMoment H raw6931step0 := by
      have heq : raw6931step0 = raw6931.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6931).symm
    injectiveMoment H raw6931step0 = injectiveMoment H raw6931step1 := by
      have heq : raw6931step1 = (fun i j => raw6931step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6931step0 permutation27 permutation17
    _ = injectiveMoment H node799 := by rfl

def raw6932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6932step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical6932 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6932 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw6932 = injectiveMoment H raw6932step0 := by
      have heq : raw6932step0 = (fun i j => raw6932 (permutation11 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6932 permutation11 permutation10
    _ = injectiveMoment H node1079 := by rfl

def raw6933 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw6933step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -1, -1, 2]]

def raw6933step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical6933 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6933 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw6933 = injectiveMoment H raw6933step0 := by
      have heq : raw6933step0 = raw6933.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6933).symm
    injectiveMoment H raw6933step0 = injectiveMoment H raw6933step1 := by
      have heq : raw6933step1 = (fun i j => raw6933step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6933step0 permutation28 permutation17
    _ = injectiveMoment H node1040 := by rfl

def raw6934 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw6934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![0, 1, -1]]

def raw6934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-2, 3, -1], ![0, -1, 1]]

def raw6934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6934 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw6934 = injectiveMoment H raw6934step0 := by
      have heq : raw6934step0 = raw6934.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6934).symm
    injectiveMoment H raw6934step0 = injectiveMoment H raw6934step1 := by
      have heq : raw6934step1 = -raw6934step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6934step0).symm
    injectiveMoment H raw6934step1 = injectiveMoment H raw6934step2 := by
      have heq : raw6934step2 = (fun i j => raw6934step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6934step1 permutation25 permutation4
    _ = injectiveMoment H node181 := by rfl

def raw6935 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw6935step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![0, -2, 2]]

def raw6935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical6935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6935 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw6935 = injectiveMoment H raw6935step0 := by
      have heq : raw6935step0 = raw6935.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6935).symm
    injectiveMoment H raw6935step0 = injectiveMoment H raw6935step1 := by
      have heq : raw6935step1 = (fun i j => raw6935step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6935step0 permutation28 permutation5
    _ = injectiveMoment H node203 := by rfl

def raw6936 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw6936step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, 1, -3], ![0, -3, 3]]

def raw6936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-2, -1, 3], ![0, 3, -3]]

def raw6936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical6936 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6936 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw6936 = injectiveMoment H raw6936step0 := by
      have heq : raw6936step0 = raw6936.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6936).symm
    injectiveMoment H raw6936step0 = injectiveMoment H raw6936step1 := by
      have heq : raw6936step1 = -raw6936step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6936step0).symm
    injectiveMoment H raw6936step1 = injectiveMoment H raw6936step2 := by
      have heq : raw6936step2 = (fun i j => raw6936step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6936step1 permutation26 permutation3
    _ = injectiveMoment H node187 := by rfl

def raw6937 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 3, -4, 1], ![1, -2, 2, -1]]

def raw6937step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, -4, 2], ![0, 1, -1]]

def raw6937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-2, 4, -2], ![0, -1, 1]]

def raw6937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical6937 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6937 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw6937 = injectiveMoment H raw6937step0 := by
      have heq : raw6937step0 = raw6937.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6937).symm
    injectiveMoment H raw6937step0 = injectiveMoment H raw6937step1 := by
      have heq : raw6937step1 = -raw6937step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6937step0).symm
    injectiveMoment H raw6937step1 = injectiveMoment H raw6937step2 := by
      have heq : raw6937step2 = (fun i j => raw6937step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6937step1 permutation25 permutation4
    _ = injectiveMoment H node149 := by rfl

def raw6938 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 3, -1, -2], ![1, -2, -1, 2]]

def raw6938step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, -1, -1], ![0, -2, 2]]

def raw6938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-2, 1, 1], ![0, 2, -2]]

def raw6938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical6938 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6938 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw6938 = injectiveMoment H raw6938step0 := by
      have heq : raw6938step0 = raw6938.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6938).symm
    injectiveMoment H raw6938step0 = injectiveMoment H raw6938step1 := by
      have heq : raw6938step1 = -raw6938step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6938step0).symm
    injectiveMoment H raw6938step1 = injectiveMoment H raw6938step2 := by
      have heq : raw6938step2 = (fun i j => raw6938step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6938step1 permutation25 permutation4
    _ = injectiveMoment H node226 := by rfl

def raw6939 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 3, 0, -3], ![1, -2, -2, 3]]

def raw6939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, 0, -2], ![0, -3, 3]]

def raw6939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-2, 0, 2], ![0, 3, -3]]

def raw6939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical6939 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6939 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw6939 = injectiveMoment H raw6939step0 := by
      have heq : raw6939step0 = raw6939.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6939).symm
    injectiveMoment H raw6939step0 = injectiveMoment H raw6939step1 := by
      have heq : raw6939step1 = -raw6939step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6939step0).symm
    injectiveMoment H raw6939step1 = injectiveMoment H raw6939step2 := by
      have heq : raw6939step2 = (fun i j => raw6939step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6939step1 permutation26 permutation3
    _ = injectiveMoment H node214 := by rfl

def raw6940 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 4, -1, -3], ![1, -3, -1, 3]]

def raw6940step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 4, -3], ![2, -1, -1], ![0, -3, 3]]

def raw6940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -4, 3], ![-2, 1, 1], ![0, 3, -3]]

def raw6940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6940 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6940 = injectiveMoment H node221 := by
  calc
    injectiveMoment H raw6940 = injectiveMoment H raw6940step0 := by
      have heq : raw6940step0 = raw6940.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6940).symm
    injectiveMoment H raw6940step0 = injectiveMoment H raw6940step1 := by
      have heq : raw6940step1 = -raw6940step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6940step0).symm
    injectiveMoment H raw6940step1 = injectiveMoment H raw6940step2 := by
      have heq : raw6940step2 = (fun i j => raw6940step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6940step1 permutation25 permutation4
    _ = injectiveMoment H node221 := by rfl

def raw6941 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -3, 0, 2], ![0, 4, -2, -2]]

def raw6941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 0, -2], ![0, 2, -2]]

def raw6941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 3, -4], ![-2, 0, 2], ![0, -2, 2]]

def raw6941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6941 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6941 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw6941 = injectiveMoment H raw6941step0 := by
      have heq : raw6941step0 = raw6941.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6941).symm
    injectiveMoment H raw6941step0 = injectiveMoment H raw6941step1 := by
      have heq : raw6941step1 = -raw6941step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6941step0).symm
    injectiveMoment H raw6941step1 = injectiveMoment H raw6941step2 := by
      have heq : raw6941step2 = (fun i j => raw6941step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6941step1 permutation25 permutation3
    _ = injectiveMoment H node201 := by rfl

def raw6942 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -3, 1, 1], ![0, 4, -3, -1]]

def raw6942step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 1, -3], ![0, 1, -1]]

def raw6942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 3, -4], ![-2, -1, 3], ![0, -1, 1]]

def raw6942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6942 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6942 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6942 = injectiveMoment H raw6942step0 := by
      have heq : raw6942step0 = raw6942.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6942).symm
    injectiveMoment H raw6942step0 = injectiveMoment H raw6942step1 := by
      have heq : raw6942step1 = -raw6942step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6942step0).symm
    injectiveMoment H raw6942step1 = injectiveMoment H raw6942step2 := by
      have heq : raw6942step2 = (fun i j => raw6942step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6942step1 permutation25 permutation3
    _ = injectiveMoment H node173 := by rfl

def raw6943 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -2, -1, 2], ![0, 3, -1, -2]]

def raw6943step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![2, -1, -1], ![0, 2, -2]]

def raw6943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 2, -3], ![-2, 1, 1], ![0, -2, 2]]

def raw6943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical6943 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6943 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw6943 = injectiveMoment H raw6943step0 := by
      have heq : raw6943step0 = raw6943.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6943).symm
    injectiveMoment H raw6943step0 = injectiveMoment H raw6943step1 := by
      have heq : raw6943step1 = -raw6943step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6943step0).symm
    injectiveMoment H raw6943step1 = injectiveMoment H raw6943step2 := by
      have heq : raw6943step2 = (fun i j => raw6943step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6943step1 permutation25 permutation3
    _ = injectiveMoment H node226 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
