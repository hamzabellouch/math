import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5920 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5920 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5920 = injectiveMoment H node870 := by
  calc
    injectiveMoment H raw5920 = injectiveMoment H raw5920step0 := by
      have heq : raw5920step0 = (fun i j => raw5920 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5920 permutation39 permutation3
    _ = injectiveMoment H node870 := by rfl

def raw5921 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw5921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5921 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5921 = injectiveMoment H node876 := by
  calc
    injectiveMoment H raw5921 = injectiveMoment H raw5921step0 := by
      have heq : raw5921step0 = (fun i j => raw5921 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5921 permutation39 permutation3
    _ = injectiveMoment H node876 := by rfl

def raw5922 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

def raw5922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5922 = injectiveMoment H node744 := by
  calc
    injectiveMoment H raw5922 = injectiveMoment H raw5922step0 := by
      have heq : raw5922step0 = (fun i j => raw5922 (permutation81 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5922 permutation81 permutation4
    _ = injectiveMoment H node744 := by rfl

def raw5923 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

theorem canonical5923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5923 = injectiveMoment H node880 := by
  rfl

def raw5924 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 2, -3]]

def raw5924step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5924 = injectiveMoment H node267 := by
  calc
    injectiveMoment H raw5924 = injectiveMoment H raw5924step0 := by
      have hz : ∀ j, raw5924 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5924step0 = (fun i j => raw5924 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5924 permutation80 hz
    _ = injectiveMoment H node267 := by rfl

def raw5925 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![1, 0, -1]]

def raw5925step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5925 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw5925 = injectiveMoment H raw5925step0 := by
      have hz : ∀ j, raw5925 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5925step0 = (fun i j => raw5925 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5925 permutation80 hz
    _ = injectiveMoment H node269 := by rfl

def raw5926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3]]

def raw5926step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5926 = injectiveMoment H node267 := by
  calc
    injectiveMoment H raw5926 = injectiveMoment H raw5926step0 := by
      have hz : ∀ j, raw5926 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5926step0 = (fun i j => raw5926 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5926 permutation104 hz
    _ = injectiveMoment H node267 := by rfl

def raw5927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5927 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5927 = injectiveMoment H node881 := by
  rfl

def raw5928 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5928 = injectiveMoment H node882 := by
  rfl

def raw5929 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5929 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5929 = injectiveMoment H node883 := by
  rfl

def raw5930 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 3, -3]]

def raw5930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5930 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5930 = injectiveMoment H node883 := by
  calc
    injectiveMoment H raw5930 = injectiveMoment H raw5930step0 := by
      have heq : raw5930step0 = (fun i j => raw5930 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5930 permutation34 permutation3
    _ = injectiveMoment H node883 := by rfl

def raw5931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 2, -2]]

def raw5931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5931 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5931 = injectiveMoment H node882 := by
  calc
    injectiveMoment H raw5931 = injectiveMoment H raw5931step0 := by
      have heq : raw5931step0 = (fun i j => raw5931 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5931 permutation34 permutation3
    _ = injectiveMoment H node882 := by rfl

def raw5932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1]]

def raw5932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5932 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5932 = injectiveMoment H node881 := by
  calc
    injectiveMoment H raw5932 = injectiveMoment H raw5932step0 := by
      have heq : raw5932step0 = (fun i j => raw5932 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5932 permutation34 permutation3
    _ = injectiveMoment H node881 := by rfl

def raw5933 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5933 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5933 = injectiveMoment H node267 := by
  rfl

def raw5934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2]]

def raw5934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5934 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5934 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw5934 = injectiveMoment H raw5934step0 := by
      have hz : ∀ j, raw5934 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5934step0 = (fun i j => raw5934 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5934 permutation104 hz
    _ = injectiveMoment H node268 := by rfl

def raw5935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1]]

def raw5935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5935 = injectiveMoment H node882 := by
  calc
    injectiveMoment H raw5935 = injectiveMoment H raw5935step0 := by
      have heq : raw5935step0 = (fun i j => raw5935 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5935 permutation35 permutation3
    _ = injectiveMoment H node882 := by rfl

def raw5936 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![0, 1, -1]]

def raw5936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5936 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5936 = injectiveMoment H node882 := by
  calc
    injectiveMoment H raw5936 = injectiveMoment H raw5936step0 := by
      have heq : raw5936step0 = (fun i j => raw5936 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5936 permutation37 permutation3
    _ = injectiveMoment H node882 := by rfl

def raw5937 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5937 = injectiveMoment H node268 := by
  rfl

def raw5938 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1]]

def raw5938step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5938 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5938 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw5938 = injectiveMoment H raw5938step0 := by
      have hz : ∀ j, raw5938 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5938step0 = (fun i j => raw5938 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5938 permutation104 hz
    _ = injectiveMoment H node269 := by rfl

def raw5939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![0, 1, -1]]

def raw5939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5939 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5939 = injectiveMoment H node883 := by
  calc
    injectiveMoment H raw5939 = injectiveMoment H raw5939step0 := by
      have heq : raw5939step0 = (fun i j => raw5939 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5939 permutation37 permutation3
    _ = injectiveMoment H node883 := by rfl

def raw5940 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5940 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5940 = injectiveMoment H node269 := by
  rfl

def raw5941 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![0, 0, 0]]

def raw5941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5941 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw5941 = injectiveMoment H raw5941step0 := by
      have hz : ∀ j, raw5941 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5941step0 = (fun i j => raw5941 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5941 permutation128 hz
    _ = injectiveMoment H node269 := by rfl

def raw5942 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical5942 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5942 = injectiveMoment H node270 := by
  rfl

def raw5943 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2]]

def raw5943step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5943 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw5943 = injectiveMoment H raw5943step0 := by
      have heq : raw5943step0 = (fun i j => raw5943 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5943 permutation10 permutation3
    _ = injectiveMoment H node268 := by rfl

def raw5944 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5944step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical5944 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5944 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw5944 = injectiveMoment H raw5944step0 := by
      have hz : ∀ j, raw5944 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5944step0 = (fun i j => raw5944 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5944 permutation57 hz
    _ = injectiveMoment H node271 := by rfl

def raw5945 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5945step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5945 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw5945 = injectiveMoment H raw5945step0 := by
      have hz : ∀ j, raw5945 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5945step0 = (fun i j => raw5945 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5945 permutation57 hz
    _ = injectiveMoment H node272 := by rfl

def raw5946 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2]]

def raw5946step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5946 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw5946 = injectiveMoment H raw5946step0 := by
      have hz : ∀ j, raw5946 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5946step0 = (fun i j => raw5946 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5946 permutation15 hz
    _ = injectiveMoment H node56 := by rfl

def raw5947 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1]]

def raw5947step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5947 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5947 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw5947 = injectiveMoment H raw5947step0 := by
      have hz : ∀ j, raw5947 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5947step0 = (fun i j => raw5947 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5947 permutation15 hz
    _ = injectiveMoment H node57 := by rfl

def raw5948 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 3, -3], ![1, -1, 0]]

def raw5948step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5948 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5948 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw5948 = injectiveMoment H raw5948step0 := by
      have hz : ∀ j, raw5948 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5948step0 = (fun i j => raw5948 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5948 permutation15 hz
    _ = injectiveMoment H node58 := by rfl

def raw5949 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![1, 2, -3]]

def raw5949step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![3, 0, -3]]

def raw5949step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw5949step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5949 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5949 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5949 = injectiveMoment H raw5949step0 := by
      have heq : raw5949step0 = raw5949.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5949).symm
    injectiveMoment H raw5949step0 = injectiveMoment H raw5949step1 := by
      have hz : ∀ i, raw5949step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw5949step1 = (fun i j => raw5949step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5949step0 permutation5 hz
    injectiveMoment H raw5949step1 = injectiveMoment H raw5949step2 := by
      have heq : raw5949step2 = (fun i j => raw5949step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5949step1 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5950 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw5950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5950 = injectiveMoment H node868 := by
  calc
    injectiveMoment H raw5950 = injectiveMoment H raw5950step0 := by
      have heq : raw5950step0 = (fun i j => raw5950 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5950 permutation39 permutation3
    _ = injectiveMoment H node868 := by rfl

def raw5951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5951 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw5951 = injectiveMoment H raw5951step0 := by
      have heq : raw5951step0 = (fun i j => raw5951 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5951 permutation39 permutation3
    _ = injectiveMoment H node872 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
