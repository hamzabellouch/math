import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5888 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5888 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5888 = injectiveMoment H node261 := by
  rfl

def raw5889 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5889step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical5889 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5889 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw5889 = injectiveMoment H raw5889step0 := by
      have heq : raw5889step0 = (fun i j => raw5889 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5889 permutation12 permutation5
    _ = injectiveMoment H node176 := by rfl

def raw5890 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, 2, -3], ![1, -2, 1]]

def raw5890step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical5890 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5890 = injectiveMoment H node260 := by
  calc
    injectiveMoment H raw5890 = injectiveMoment H raw5890step0 := by
      have heq : raw5890step0 = (fun i j => raw5890 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5890 permutation10 permutation3
    _ = injectiveMoment H node260 := by rfl

def raw5891 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, 0, -2]]

def raw5891step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5891 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw5891 = injectiveMoment H raw5891step0 := by
      have heq : raw5891step0 = (fun i j => raw5891 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5891 permutation4 permutation5
    _ = injectiveMoment H node36 := by rfl

def raw5892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5892 = injectiveMoment H node874 := by
  rfl

def raw5893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw5893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5893 = injectiveMoment H node874 := by
  calc
    injectiveMoment H raw5893 = injectiveMoment H raw5893step0 := by
      have heq : raw5893step0 = (fun i j => raw5893 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5893 permutation34 permutation3
    _ = injectiveMoment H node874 := by rfl

def raw5894 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![2, 1, -3]]

def raw5894step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![0, 2, -2], ![-2, -1, 3]]

def raw5894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 2, -3]]

theorem canonical5894 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5894 = injectiveMoment H node183 := by
  calc
    injectiveMoment H raw5894 = injectiveMoment H raw5894step0 := by
      have heq : raw5894step0 = -raw5894 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5894).symm
    injectiveMoment H raw5894step0 = injectiveMoment H raw5894step1 := by
      have heq : raw5894step1 = (fun i j => raw5894step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5894step0 permutation32 permutation3
    _ = injectiveMoment H node183 := by rfl

def raw5895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5895 = injectiveMoment H node876 := by
  rfl

def raw5896 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw5896step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5896 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5896 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw5896 = injectiveMoment H raw5896step0 := by
      have hz : ∀ j, raw5896 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5896step0 = (fun i j => raw5896 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5896 permutation80 hz
    _ = injectiveMoment H node263 := by rfl

def raw5897 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw5897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5897 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5897 = injectiveMoment H node875 := by
  calc
    injectiveMoment H raw5897 = injectiveMoment H raw5897step0 := by
      have heq : raw5897step0 = (fun i j => raw5897 (permutation58 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5897 permutation58 permutation4
    _ = injectiveMoment H node875 := by rfl

def raw5898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw5898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5898 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5898 = injectiveMoment H node876 := by
  calc
    injectiveMoment H raw5898 = injectiveMoment H raw5898step0 := by
      have heq : raw5898step0 = (fun i j => raw5898 (permutation57 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5898 permutation57 permutation4
    _ = injectiveMoment H node876 := by rfl

def raw5899 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical5899 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5899 = injectiveMoment H node262 := by
  rfl

def raw5900 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5900 = injectiveMoment H node263 := by
  rfl

def raw5901 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0]]

def raw5901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5901 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5901 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw5901 = injectiveMoment H raw5901step0 := by
      have heq : raw5901step0 = (fun i j => raw5901 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5901 permutation10 permutation3
    _ = injectiveMoment H node263 := by rfl

def raw5902 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![2, -1, -1]]

def raw5902step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 1, 1]]

def raw5902step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical5902 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5902 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw5902 = injectiveMoment H raw5902step0 := by
      have heq : raw5902step0 = -raw5902 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5902).symm
    injectiveMoment H raw5902step0 = injectiveMoment H raw5902step1 := by
      have heq : raw5902step1 = (fun i j => raw5902step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5902step0 permutation8 permutation3
    _ = injectiveMoment H node43 := by rfl

def raw5903 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5903 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5903 = injectiveMoment H node877 := by
  rfl

def raw5904 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -2, 2], ![2, 0, -2]]

def raw5904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -4, 3], ![0, 2, -2], ![-2, 0, 2]]

def raw5904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

theorem canonical5904 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5904 = injectiveMoment H node211 := by
  calc
    injectiveMoment H raw5904 = injectiveMoment H raw5904step0 := by
      have heq : raw5904step0 = -raw5904 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5904).symm
    injectiveMoment H raw5904step0 = injectiveMoment H raw5904step1 := by
      have heq : raw5904step1 = (fun i j => raw5904step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5904step0 permutation32 permutation3
    _ = injectiveMoment H node211 := by rfl

def raw5905 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw5905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5905 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5905 = injectiveMoment H node744 := by
  calc
    injectiveMoment H raw5905 = injectiveMoment H raw5905step0 := by
      have heq : raw5905step0 = (fun i j => raw5905 (permutation58 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5905 permutation58 permutation4
    _ = injectiveMoment H node744 := by rfl

def raw5906 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]

def raw5906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5906 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5906 = injectiveMoment H node744 := by
  calc
    injectiveMoment H raw5906 = injectiveMoment H raw5906step0 := by
      have heq : raw5906step0 = (fun i j => raw5906 (permutation57 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5906 permutation57 permutation4
    _ = injectiveMoment H node744 := by rfl

def raw5907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![1, -2, 1], ![1, 0, -1]]

def raw5907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5907 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5907 = injectiveMoment H node247 := by
  calc
    injectiveMoment H raw5907 = injectiveMoment H raw5907step0 := by
      have heq : raw5907step0 = (fun i j => raw5907 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5907 permutation16 permutation4
    _ = injectiveMoment H node247 := by rfl

def raw5908 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0]]

def raw5908step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5908 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5908 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw5908 = injectiveMoment H raw5908step0 := by
      have heq : raw5908step0 = (fun i j => raw5908 (permutation15 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5908 permutation15 permutation4
    _ = injectiveMoment H node248 := by rfl

def raw5909 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![2, -2, 0]]

def raw5909step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 4, -2], ![3, -3, 0]]

def raw5909step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical5909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5909 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw5909 = injectiveMoment H raw5909step0 := by
      have heq : raw5909step0 = raw5909.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5909).symm
    injectiveMoment H raw5909step0 = injectiveMoment H raw5909step1 := by
      have heq : raw5909step1 = (fun i j => raw5909step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5909step0 permutation6 permutation7
    _ = injectiveMoment H node32 := by rfl

def raw5910 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5910 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5910 = injectiveMoment H node878 := by
  rfl

def raw5911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5911 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5911 = injectiveMoment H node879 := by
  rfl

def raw5912 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![1, 3, -4]]

def raw5912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -3, 4]]

def raw5912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 2, -2], ![1, 2, -3]]

theorem canonical5912 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5912 = injectiveMoment H node250 := by
  calc
    injectiveMoment H raw5912 = injectiveMoment H raw5912step0 := by
      have heq : raw5912step0 = -raw5912 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5912).symm
    injectiveMoment H raw5912step0 = injectiveMoment H raw5912step1 := by
      have heq : raw5912step1 = (fun i j => raw5912step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5912step0 permutation32 permutation3
    _ = injectiveMoment H node250 := by rfl

def raw5913 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 2, -2], ![1, 2, -3]]

theorem canonical5913 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5913 = injectiveMoment H node264 := by
  rfl

def raw5914 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

theorem canonical5914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5914 = injectiveMoment H node265 := by
  rfl

def raw5915 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

theorem canonical5915 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5915 = injectiveMoment H node266 := by
  rfl

def raw5916 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![1, 4, -5]]

def raw5916step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![-1, -4, 5]]

def raw5916step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

theorem canonical5916 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5916 = injectiveMoment H node48 := by
  calc
    injectiveMoment H raw5916 = injectiveMoment H raw5916step0 := by
      have heq : raw5916step0 = -raw5916 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5916).symm
    injectiveMoment H raw5916step0 = injectiveMoment H raw5916step1 := by
      have heq : raw5916step1 = (fun i j => raw5916step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5916step0 permutation8 permutation3
    _ = injectiveMoment H node48 := by rfl

def raw5917 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw5917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw5917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5917 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5917 = injectiveMoment H node862 := by
  calc
    injectiveMoment H raw5917 = injectiveMoment H raw5917step0 := by
      have heq : raw5917step0 = -raw5917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5917).symm
    injectiveMoment H raw5917step0 = injectiveMoment H raw5917step1 := by
      have heq : raw5917step1 = (fun i j => raw5917step0 (permutation148 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5917step0 permutation148 permutation3
    _ = injectiveMoment H node862 := by rfl

def raw5918 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw5918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5918 = injectiveMoment H node866 := by
  calc
    injectiveMoment H raw5918 = injectiveMoment H raw5918step0 := by
      have heq : raw5918step0 = (fun i j => raw5918 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5918 permutation39 permutation3
    _ = injectiveMoment H node866 := by rfl

def raw5919 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw5919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw5919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical5919 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5919 = injectiveMoment H node867 := by
  calc
    injectiveMoment H raw5919 = injectiveMoment H raw5919step0 := by
      have heq : raw5919step0 = -raw5919 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5919).symm
    injectiveMoment H raw5919step0 = injectiveMoment H raw5919step1 := by
      have heq : raw5919step1 = (fun i j => raw5919step0 (permutation148 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5919step0 permutation148 permutation3
    _ = injectiveMoment H node867 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
