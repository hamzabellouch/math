import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8896 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 2, -1, 1], ![2, -1, -1, 0]]

def raw8896step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![2, -1, -1], ![-1, 1, 0]]

def raw8896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -2, 1], ![-2, 1, 1], ![1, -1, 0]]

def raw8896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical8896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8896 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw8896 = injectiveMoment H raw8896step0 := by
      have heq : raw8896step0 = raw8896.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8896).symm
    injectiveMoment H raw8896step0 = injectiveMoment H raw8896step1 := by
      have heq : raw8896step1 = -raw8896step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8896step0).symm
    injectiveMoment H raw8896step1 = injectiveMoment H raw8896step2 := by
      have heq : raw8896step2 = (fun i j => raw8896step1 (permutation14 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8896step1 permutation14 permutation7
    _ = injectiveMoment H node210 := by rfl

def raw8897 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 2, 1, -1], ![2, -1, -3, 2]]

def raw8897step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![2, 1, -3], ![-1, -1, 2]]

def raw8897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -2, 1], ![-2, -1, 3], ![1, 1, -2]]

def raw8897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical8897 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8897 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw8897 = injectiveMoment H raw8897step0 := by
      have heq : raw8897step0 = raw8897.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8897).symm
    injectiveMoment H raw8897step0 = injectiveMoment H raw8897step1 := by
      have heq : raw8897step1 = -raw8897step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8897step0).symm
    injectiveMoment H raw8897step1 = injectiveMoment H raw8897step2 := by
      have heq : raw8897step2 = (fun i j => raw8897step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8897step1 permutation21 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw8898 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 3, -1, 0], ![2, -2, -1, 1]]

def raw8898step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1]]

def raw8898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -3, 2], ![-2, 1, 1], ![1, 0, -1]]

def raw8898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8898 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8898 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw8898 = injectiveMoment H raw8898step0 := by
      have heq : raw8898step0 = raw8898.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8898).symm
    injectiveMoment H raw8898step0 = injectiveMoment H raw8898step1 := by
      have heq : raw8898step1 = -raw8898step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8898step0).symm
    injectiveMoment H raw8898step1 = injectiveMoment H raw8898step2 := by
      have heq : raw8898step2 = (fun i j => raw8898step1 (permutation22 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8898step1 permutation22 permutation4
    _ = injectiveMoment H node226 := by rfl

def raw8899 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 3, 0, -1], ![2, -2, -2, 2]]

def raw8899step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![2, 0, -2], ![-1, -1, 2]]

def raw8899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -3, 2], ![-2, 0, 2], ![1, 1, -2]]

def raw8899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical8899 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8899 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw8899 = injectiveMoment H raw8899step0 := by
      have heq : raw8899step0 = raw8899.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8899).symm
    injectiveMoment H raw8899step0 = injectiveMoment H raw8899step1 := by
      have heq : raw8899step1 = -raw8899step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8899step0).symm
    injectiveMoment H raw8899step1 = injectiveMoment H raw8899step2 := by
      have heq : raw8899step2 = (fun i j => raw8899step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8899step1 permutation21 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw8900 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 4, -1, -1], ![2, -3, -1, 2]]

def raw8900step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 4, -3], ![2, -1, -1], ![-1, -1, 2]]

def raw8900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -4, 3], ![-2, 1, 1], ![1, 1, -2]]

def raw8900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8900 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8900 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw8900 = injectiveMoment H raw8900step0 := by
      have heq : raw8900step0 = raw8900.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8900).symm
    injectiveMoment H raw8900step0 = injectiveMoment H raw8900step1 := by
      have heq : raw8900step1 = -raw8900step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8900step0).symm
    injectiveMoment H raw8900step1 = injectiveMoment H raw8900step2 := by
      have heq : raw8900step2 = (fun i j => raw8900step1 (permutation22 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8900step1 permutation22 permutation4
    _ = injectiveMoment H node225 := by rfl

def raw8901 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, -2, 2, 1], ![1, 3, -4, 0]]

def raw8901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![2, 2, -4], ![-1, 1, 0]]

def raw8901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 2, -3], ![-2, -2, 4], ![1, -1, 0]]

def raw8901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8901 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8901 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw8901 = injectiveMoment H raw8901step0 := by
      have heq : raw8901step0 = raw8901.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8901).symm
    injectiveMoment H raw8901step0 = injectiveMoment H raw8901step1 := by
      have heq : raw8901step1 = -raw8901step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8901step0).symm
    injectiveMoment H raw8901step1 = injectiveMoment H raw8901step2 := by
      have heq : raw8901step2 = (fun i j => raw8901step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8901step1 permutation22 permutation3
    _ = injectiveMoment H node149 := by rfl

def raw8902 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, -1, -2, 4], ![1, 2, 0, -3]]

def raw8902step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![2, -2, 0], ![-1, 4, -3]]

def raw8902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![-2, 2, 0], ![1, -4, 3]]

def raw8902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8902 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8902 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw8902 = injectiveMoment H raw8902step0 := by
      have heq : raw8902step0 = raw8902.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8902).symm
    injectiveMoment H raw8902step0 = injectiveMoment H raw8902step1 := by
      have heq : raw8902step1 = -raw8902step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8902step0).symm
    injectiveMoment H raw8902step1 = injectiveMoment H raw8902step2 := by
      have heq : raw8902step2 = (fun i j => raw8902step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8902step1 permutation21 permutation4
    _ = injectiveMoment H node206 := by rfl

def raw8903 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, -1, -1, 3], ![1, 2, -1, -2]]

def raw8903step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![2, -1, -1], ![-1, 3, -2]]

def raw8903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![-2, 1, 1], ![1, -3, 2]]

def raw8903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical8903 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8903 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw8903 = injectiveMoment H raw8903step0 := by
      have heq : raw8903step0 = raw8903.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8903).symm
    injectiveMoment H raw8903step0 = injectiveMoment H raw8903step1 := by
      have heq : raw8903step1 = -raw8903step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8903step0).symm
    injectiveMoment H raw8903step1 = injectiveMoment H raw8903step2 := by
      have heq : raw8903step2 = (fun i j => raw8903step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8903step1 permutation21 permutation4
    _ = injectiveMoment H node229 := by rfl

def raw8904 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, -1, 3, -1], ![1, 2, -5, 2]]

def raw8904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![2, 3, -5], ![-1, -1, 2]]

def raw8904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![-2, -3, 5], ![1, 1, -2]]

def raw8904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical8904 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8904 = injectiveMoment H node124 := by
  calc
    injectiveMoment H raw8904 = injectiveMoment H raw8904step0 := by
      have heq : raw8904step0 = raw8904.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8904).symm
    injectiveMoment H raw8904step0 = injectiveMoment H raw8904step1 := by
      have heq : raw8904step1 = -raw8904step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8904step0).symm
    injectiveMoment H raw8904step1 = injectiveMoment H raw8904step2 := by
      have heq : raw8904step2 = (fun i j => raw8904step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8904step1 permutation21 permutation3
    _ = injectiveMoment H node124 := by rfl

def raw8905 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw8905step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical8905 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8905 = injectiveMoment H node1248 := by
  calc
    injectiveMoment H raw8905 = injectiveMoment H raw8905step0 := by
      have heq : raw8905step0 = (fun i j => raw8905 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8905 permutation15 permutation9
    _ = injectiveMoment H node1248 := by rfl

def raw8906 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8906step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw8906step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw8906step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical8906 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8906 = injectiveMoment H node816 := by
  calc
    injectiveMoment H raw8906 = injectiveMoment H raw8906step0 := by
      have heq : raw8906step0 = raw8906.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8906).symm
    injectiveMoment H raw8906step0 = injectiveMoment H raw8906step1 := by
      have heq : raw8906step1 = -raw8906step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8906step0).symm
    injectiveMoment H raw8906step1 = injectiveMoment H raw8906step2 := by
      have heq : raw8906step2 = (fun i j => raw8906step1 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8906step1 permutation24 permutation15
    _ = injectiveMoment H node816 := by rfl

def raw8907 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8907step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, -3, 1, 0], ![-1, 3, -2, 0]]

def raw8907step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical8907 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8907 = injectiveMoment H node1094 := by
  calc
    injectiveMoment H raw8907 = injectiveMoment H raw8907step0 := by
      have heq : raw8907step0 = raw8907.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8907).symm
    injectiveMoment H raw8907step0 = injectiveMoment H raw8907step1 := by
      have heq : raw8907step1 = (fun i j => raw8907step0 (permutation20 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8907step0 permutation20 permutation28
    _ = injectiveMoment H node1094 := by rfl

def raw8908 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8908step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![-1, 0, -1, 2]]

def raw8908step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 0, 1, -2]]

def raw8908step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical8908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8908 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw8908 = injectiveMoment H raw8908step0 := by
      have heq : raw8908step0 = raw8908.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8908).symm
    injectiveMoment H raw8908step0 = injectiveMoment H raw8908step1 := by
      have heq : raw8908step1 = -raw8908step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8908step0).symm
    injectiveMoment H raw8908step1 = injectiveMoment H raw8908step2 := by
      have heq : raw8908step2 = (fun i j => raw8908step1 (permutation17 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8908step1 permutation17 permutation23
    _ = injectiveMoment H node1110 := by rfl

def raw8909 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8909step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw8909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![-2, 0, 2], ![1, 1, -2]]

def raw8909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical8909 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8909 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw8909 = injectiveMoment H raw8909step0 := by
      have heq : raw8909step0 = raw8909.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8909).symm
    injectiveMoment H raw8909step0 = injectiveMoment H raw8909step1 := by
      have heq : raw8909step1 = -raw8909step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8909step0).symm
    injectiveMoment H raw8909step1 = injectiveMoment H raw8909step2 := by
      have heq : raw8909step2 = (fun i j => raw8909step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8909step1 permutation21 permutation3
    _ = injectiveMoment H node210 := by rfl

def raw8910 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 2, 1, -2], ![1, -1, -3, 3]]

def raw8910step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![2, 1, -3], ![-1, -2, 3]]

def raw8910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![-2, -1, 3], ![1, 2, -3]]

def raw8910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical8910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8910 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw8910 = injectiveMoment H raw8910step0 := by
      have heq : raw8910step0 = raw8910.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8910).symm
    injectiveMoment H raw8910step0 = injectiveMoment H raw8910step1 := by
      have heq : raw8910step1 = -raw8910step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8910step0).symm
    injectiveMoment H raw8910step1 = injectiveMoment H raw8910step2 := by
      have heq : raw8910step2 = (fun i j => raw8910step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8910step1 permutation21 permutation3
    _ = injectiveMoment H node180 := by rfl

def raw8911 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 3, -1, -1], ![1, -2, -1, 2]]

def raw8911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![-1, -1, 2]]

def raw8911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -3, 2], ![-2, 1, 1], ![1, 1, -2]]

def raw8911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical8911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8911 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw8911 = injectiveMoment H raw8911step0 := by
      have heq : raw8911step0 = raw8911.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8911).symm
    injectiveMoment H raw8911step0 = injectiveMoment H raw8911step1 := by
      have heq : raw8911step1 = -raw8911step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8911step0).symm
    injectiveMoment H raw8911step1 = injectiveMoment H raw8911step2 := by
      have heq : raw8911step2 = (fun i j => raw8911step1 (permutation22 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8911step1 permutation22 permutation4
    _ = injectiveMoment H node229 := by rfl

def raw8912 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 3, 0, -2], ![1, -2, -2, 3]]

def raw8912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 3, -2], ![2, 0, -2], ![-1, -2, 3]]

def raw8912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -3, 2], ![-2, 0, 2], ![1, 2, -3]]

def raw8912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical8912 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8912 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw8912 = injectiveMoment H raw8912step0 := by
      have heq : raw8912step0 = raw8912.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8912).symm
    injectiveMoment H raw8912step0 = injectiveMoment H raw8912step1 := by
      have heq : raw8912step1 = -raw8912step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8912step0).symm
    injectiveMoment H raw8912step1 = injectiveMoment H raw8912step2 := by
      have heq : raw8912step2 = (fun i j => raw8912step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8912step1 permutation21 permutation3
    _ = injectiveMoment H node209 := by rfl

def raw8913 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 4, -1, -2], ![1, -3, -1, 3]]

def raw8913step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 4, -3], ![2, -1, -1], ![-1, -2, 3]]

def raw8913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -4, 3], ![-2, 1, 1], ![1, 2, -3]]

def raw8913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical8913 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8913 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw8913 = injectiveMoment H raw8913step0 := by
      have heq : raw8913step0 = raw8913.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8913).symm
    injectiveMoment H raw8913step0 = injectiveMoment H raw8913step1 := by
      have heq : raw8913step1 = -raw8913step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8913step0).symm
    injectiveMoment H raw8913step1 = injectiveMoment H raw8913step2 := by
      have heq : raw8913step2 = (fun i j => raw8913step1 (permutation22 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8913step1 permutation22 permutation4
    _ = injectiveMoment H node228 := by rfl

def raw8914 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3]]

def raw8914step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 3, -4], ![0, -2, -1, 3]]

def raw8914step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![1, 3, -4], ![-2, -1, 3]]

def raw8914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8914 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8914 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw8914 = injectiveMoment H raw8914step0 := by
      have heq : raw8914step0 = -raw8914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8914).symm
    injectiveMoment H raw8914step0 = injectiveMoment H raw8914step1 := by
      have hz : ∀ i, raw8914step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8914step1 = (fun i j => raw8914step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8914step0 permutation9 hz
    injectiveMoment H raw8914step1 = injectiveMoment H raw8914step2 := by
      have heq : raw8914step2 = (fun i j => raw8914step1 (permutation7 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8914step1 permutation7 permutation3
    _ = injectiveMoment H node40 := by rfl

def raw8915 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, -1, -2, 2]]

def raw8915step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 0, 1, -1], ![1, -2, -1, 2], ![-1, 1, 2, -2]]

def raw8915step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical8915 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8915 = injectiveMoment H node1336 := by
  calc
    injectiveMoment H raw8915 = injectiveMoment H raw8915step0 := by
      have heq : raw8915step0 = -raw8915 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8915).symm
    injectiveMoment H raw8915step0 = injectiveMoment H raw8915step1 := by
      have heq : raw8915step1 = (fun i j => raw8915step0 (permutation29 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8915step0 permutation29 permutation10
    _ = injectiveMoment H node1336 := by rfl

def raw8916 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, -1, -2, 3]]

def raw8916step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 1, 2, -3]]

def raw8916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 1, -1], ![-2, -1, 3], ![1, 2, -3]]

def raw8916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical8916 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8916 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw8916 = injectiveMoment H raw8916step0 := by
      have heq : raw8916step0 = -raw8916 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8916).symm
    injectiveMoment H raw8916step0 = injectiveMoment H raw8916step1 := by
      have hz : ∀ i, raw8916step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8916step1 = (fun i j => raw8916step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8916step0 permutation9 hz
    injectiveMoment H raw8916step1 = injectiveMoment H raw8916step2 := by
      have heq : raw8916step2 = (fun i j => raw8916step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8916step1 permutation23 permutation3
    _ = injectiveMoment H node180 := by rfl

def raw8917 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, -3, 3]]

def raw8917step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![2, 1, 0, -3], ![-1, -1, -1, 3]]

def raw8917step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-2, -1, 0, 3], ![1, 1, 1, -3]]

def raw8917step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

theorem canonical8917 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8917 = injectiveMoment H node800 := by
  calc
    injectiveMoment H raw8917 = injectiveMoment H raw8917step0 := by
      have heq : raw8917step0 = raw8917.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8917).symm
    injectiveMoment H raw8917step0 = injectiveMoment H raw8917step1 := by
      have heq : raw8917step1 = -raw8917step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8917step0).symm
    injectiveMoment H raw8917step1 = injectiveMoment H raw8917step2 := by
      have heq : raw8917step2 = (fun i j => raw8917step1 (permutation21 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8917step1 permutation21 permutation15
    _ = injectiveMoment H node800 := by rfl

def raw8918 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -3, 4]]

def raw8918step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![0, 1, 3, -4]]

def raw8918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 0, 2], ![1, 3, -4]]

def raw8918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8918 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8918 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw8918 = injectiveMoment H raw8918step0 := by
      have heq : raw8918step0 = -raw8918 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8918).symm
    injectiveMoment H raw8918step0 = injectiveMoment H raw8918step1 := by
      have hz : ∀ i, raw8918step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8918step1 = (fun i j => raw8918step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8918step0 permutation9 hz
    injectiveMoment H raw8918step1 = injectiveMoment H raw8918step2 := by
      have heq : raw8918step2 = (fun i j => raw8918step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8918step1 permutation23 permutation3
    _ = injectiveMoment H node206 := by rfl

def raw8919 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 1, -3, 2], ![-1, 1, 1, -1], ![1, -1, 0, 0]]

def raw8919step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8919 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8919 = injectiveMoment H node1099 := by
  calc
    injectiveMoment H raw8919 = injectiveMoment H raw8919step0 := by
      have heq : raw8919step0 = (fun i j => raw8919 (permutation21 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8919 permutation21 permutation13
    _ = injectiveMoment H node1099 := by rfl

def raw8920 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![0, -1, 0, 1]]

def raw8920step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, -1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1]]

def raw8920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, 3, -2], ![-1, -1, 2], ![1, 0, -1]]

def raw8920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8920 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8920 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw8920 = injectiveMoment H raw8920step0 := by
      have heq : raw8920step0 = -raw8920 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8920).symm
    injectiveMoment H raw8920step0 = injectiveMoment H raw8920step1 := by
      have hz : ∀ i, raw8920step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8920step1 = (fun i j => raw8920step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8920step0 permutation9 hz
    injectiveMoment H raw8920step1 = injectiveMoment H raw8920step2 := by
      have heq : raw8920step2 = (fun i j => raw8920step1 (permutation18 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8920step1 permutation18 permutation4
    _ = injectiveMoment H node261 := by rfl

def raw8921 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -1, -2, 2]]

def raw8921step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![-1, -1, 0, 2]]

def raw8921step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 1, 0, -2]]

def raw8921step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical8921 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8921 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw8921 = injectiveMoment H raw8921step0 := by
      have heq : raw8921step0 = raw8921.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8921).symm
    injectiveMoment H raw8921step0 = injectiveMoment H raw8921step1 := by
      have heq : raw8921step1 = -raw8921step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8921step0).symm
    injectiveMoment H raw8921step1 = injectiveMoment H raw8921step2 := by
      have heq : raw8921step2 = (fun i j => raw8921step1 (permutation17 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8921step1 permutation17 permutation17
    _ = injectiveMoment H node1110 := by rfl

def raw8922 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -2, 3]]

def raw8922step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3]]

def raw8922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8922 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw8922 = injectiveMoment H raw8922step0 := by
      have hz : ∀ i, raw8922 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8922step0 = (fun i j => raw8922 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8922 permutation9 hz
    injectiveMoment H raw8922step0 = injectiveMoment H raw8922step1 := by
      have heq : raw8922step1 = (fun i j => raw8922step0 (permutation30 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8922step0 permutation30 permutation5
    _ = injectiveMoment H node176 := by rfl

def raw8923 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8923step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![2, 0, -2], ![-1, -2, 3]]

def raw8923step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8923 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8923 = injectiveMoment H raw8923step0 := by
      have hz : ∀ i, raw8923 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8923step0 = (fun i j => raw8923 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8923 permutation9 hz
    injectiveMoment H raw8923step0 = injectiveMoment H raw8923step1 := by
      have heq : raw8923step1 = (fun i j => raw8923step0 (permutation8 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8923step0 permutation8 permutation5
    _ = injectiveMoment H node36 := by rfl

def raw8924 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 2, 1, -3], ![0, -1, -3, 4]]

def raw8924step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, -2, -1, 3], ![0, 1, 3, -4]]

def raw8924step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![-2, -1, 3], ![1, 3, -4]]

def raw8924step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8924 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8924 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw8924 = injectiveMoment H raw8924step0 := by
      have heq : raw8924step0 = -raw8924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8924).symm
    injectiveMoment H raw8924step0 = injectiveMoment H raw8924step1 := by
      have hz : ∀ i, raw8924step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8924step1 = (fun i j => raw8924step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8924step0 permutation9 hz
    injectiveMoment H raw8924step1 = injectiveMoment H raw8924step2 := by
      have heq : raw8924step2 = (fun i j => raw8924step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8924step1 permutation5 permutation3
    _ = injectiveMoment H node40 := by rfl

def raw8925 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, -3, 0, 2], ![-1, 4, -2, -1]]

def raw8925step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![2, 0, -2], ![-1, 2, -1]]

def raw8925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 3, -4], ![-2, 0, 2], ![1, -2, 1]]

def raw8925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8925 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8925 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw8925 = injectiveMoment H raw8925step0 := by
      have heq : raw8925step0 = raw8925.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8925).symm
    injectiveMoment H raw8925step0 = injectiveMoment H raw8925step1 := by
      have heq : raw8925step1 = -raw8925step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8925step0).symm
    injectiveMoment H raw8925step1 = injectiveMoment H raw8925step2 := by
      have heq : raw8925step2 = (fun i j => raw8925step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8925step1 permutation22 permutation3
    _ = injectiveMoment H node206 := by rfl

def raw8926 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, -2, 1, 0], ![-1, 3, -3, 1]]

def raw8926step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![2, 1, -3], ![-1, 0, 1]]

def raw8926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8926 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw8926 = injectiveMoment H raw8926step0 := by
      have heq : raw8926step0 = raw8926.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8926).symm
    injectiveMoment H raw8926step0 = injectiveMoment H raw8926step1 := by
      have heq : raw8926step1 = (fun i j => raw8926step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8926step0 permutation19 permutation5
    _ = injectiveMoment H node174 := by rfl

def raw8927 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, -1, 0, 0], ![-1, 2, -2, 1]]

def raw8927step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![-1, 0, 1]]

def raw8927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8927 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8927 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw8927 = injectiveMoment H raw8927step0 := by
      have heq : raw8927step0 = raw8927.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8927).symm
    injectiveMoment H raw8927step0 = injectiveMoment H raw8927step1 := by
      have heq : raw8927step1 = (fun i j => raw8927step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8927step0 permutation20 permutation5
    _ = injectiveMoment H node284 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
