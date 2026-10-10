import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9920 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, -1, 1, 2]]

def raw9920step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical9920 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9920 = injectiveMoment H node3086 := by
  calc
    injectiveMoment H raw9920 = injectiveMoment H raw9920step0 := by
      have heq : raw9920step0 = (fun i j => raw9920 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9920 permutation308 permutation9
    _ = injectiveMoment H node3086 := by rfl

def raw9921 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3]]

def raw9921step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, 0, -3]]

def raw9921step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical9921 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9921 = injectiveMoment H node3440 := by
  calc
    injectiveMoment H raw9921 = injectiveMoment H raw9921step0 := by
      have heq : raw9921step0 = -raw9921 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9921).symm
    injectiveMoment H raw9921step0 = injectiveMoment H raw9921step1 := by
      have heq : raw9921step1 = (fun i j => raw9921step0 (permutation152 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9921step0 permutation152 permutation23
    _ = injectiveMoment H node3440 := by rfl

def raw9922 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, -1, 4]]

def raw9922step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9922 = injectiveMoment H node3334 := by
  calc
    injectiveMoment H raw9922 = injectiveMoment H raw9922step0 := by
      have heq : raw9922step0 = (fun i j => raw9922 (permutation340 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9922 permutation340 permutation21
    _ = injectiveMoment H node3334 := by rfl

def raw9923 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -2, 5]]

def raw9923step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical9923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9923 = injectiveMoment H node2864 := by
  calc
    injectiveMoment H raw9923 = injectiveMoment H raw9923step0 := by
      have heq : raw9923step0 = (fun i j => raw9923 (permutation339 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9923 permutation339 permutation21
    _ = injectiveMoment H node2864 := by rfl

def raw9924 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9924step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical9924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9924 = injectiveMoment H node3186 := by
  calc
    injectiveMoment H raw9924 = injectiveMoment H raw9924step0 := by
      have heq : raw9924step0 = (fun i j => raw9924 (permutation259 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9924 permutation259 permutation10
    _ = injectiveMoment H node3186 := by rfl

def raw9925 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9925step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9925 = injectiveMoment H node2887 := by
  calc
    injectiveMoment H raw9925 = injectiveMoment H raw9925step0 := by
      have heq : raw9925step0 = (fun i j => raw9925 (permutation324 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9925 permutation324 permutation15
    _ = injectiveMoment H node2887 := by rfl

def raw9926 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9926step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9926 = injectiveMoment H node2877 := by
  calc
    injectiveMoment H raw9926 = injectiveMoment H raw9926step0 := by
      have heq : raw9926step0 = (fun i j => raw9926 (permutation324 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9926 permutation324 permutation15
    _ = injectiveMoment H node2877 := by rfl

def raw9927 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, -2, -1, 2]]

def raw9927step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9927 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9927 = injectiveMoment H node3042 := by
  calc
    injectiveMoment H raw9927 = injectiveMoment H raw9927step0 := by
      have heq : raw9927step0 = (fun i j => raw9927 (permutation389 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9927 permutation389 permutation17
    _ = injectiveMoment H node3042 := by rfl

def raw9928 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -2, 3]]

def raw9928step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical9928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9928 = injectiveMoment H node3187 := by
  calc
    injectiveMoment H raw9928 = injectiveMoment H raw9928step0 := by
      have heq : raw9928step0 = (fun i j => raw9928 (permutation259 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9928 permutation259 permutation10
    _ = injectiveMoment H node3187 := by rfl

def raw9929 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -2, 1, 3]]

def raw9929step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9929 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9929 = injectiveMoment H node2888 := by
  calc
    injectiveMoment H raw9929 = injectiveMoment H raw9929step0 := by
      have heq : raw9929step0 = (fun i j => raw9929 (permutation324 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9929 permutation324 permutation15
    _ = injectiveMoment H node2888 := by rfl

def raw9930 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 0, 4]]

def raw9930step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![2, 2, 0, -4]]

def raw9930step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical9930 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9930 = injectiveMoment H node3439 := by
  calc
    injectiveMoment H raw9930 = injectiveMoment H raw9930step0 := by
      have heq : raw9930step0 = -raw9930 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9930).symm
    injectiveMoment H raw9930step0 = injectiveMoment H raw9930step1 := by
      have heq : raw9930step1 = (fun i j => raw9930step0 (permutation154 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9930step0 permutation154 permutation23
    _ = injectiveMoment H node3439 := by rfl

def raw9931 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, -1, 5]]

def raw9931step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9931 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9931 = injectiveMoment H node2867 := by
  calc
    injectiveMoment H raw9931 = injectiveMoment H raw9931step0 := by
      have heq : raw9931step0 = (fun i j => raw9931 (permutation324 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9931 permutation324 permutation15
    _ = injectiveMoment H node2867 := by rfl

def raw9932 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9932step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9932 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9932 = injectiveMoment H node3352 := by
  calc
    injectiveMoment H raw9932 = injectiveMoment H raw9932step0 := by
      have heq : raw9932step0 = (fun i j => raw9932 (permutation363 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9932 permutation363 permutation17
    _ = injectiveMoment H node3352 := by rfl

def raw9933 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9933step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9933 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9933 = injectiveMoment H node3233 := by
  calc
    injectiveMoment H raw9933 = injectiveMoment H raw9933step0 := by
      have heq : raw9933step0 = (fun i j => raw9933 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9933 permutation395 permutation9
    _ = injectiveMoment H node3233 := by rfl

def raw9934 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9934step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9934 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9934 = injectiveMoment H node3354 := by
  calc
    injectiveMoment H raw9934 = injectiveMoment H raw9934step0 := by
      have heq : raw9934step0 = (fun i j => raw9934 (permutation363 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9934 permutation363 permutation17
    _ = injectiveMoment H node3354 := by rfl

def raw9935 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9935step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9935 = injectiveMoment H node3234 := by
  calc
    injectiveMoment H raw9935 = injectiveMoment H raw9935step0 := by
      have heq : raw9935step0 = (fun i j => raw9935 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9935 permutation395 permutation9
    _ = injectiveMoment H node3234 := by rfl

def raw9936 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw9936step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9936 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9936 = injectiveMoment H node3373 := by
  calc
    injectiveMoment H raw9936 = injectiveMoment H raw9936step0 := by
      have heq : raw9936step0 = (fun i j => raw9936 (permutation401 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9936 permutation401 permutation21
    _ = injectiveMoment H node3373 := by rfl

def raw9937 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw9937step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9937 = injectiveMoment H node2914 := by
  calc
    injectiveMoment H raw9937 = injectiveMoment H raw9937step0 := by
      have heq : raw9937step0 = (fun i j => raw9937 (permutation364 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9937 permutation364 permutation23
    _ = injectiveMoment H node2914 := by rfl

def raw9938 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 1, 0], ![-2, 1, -2, 3]]

def raw9938step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9938 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9938 = injectiveMoment H node2889 := by
  calc
    injectiveMoment H raw9938 = injectiveMoment H raw9938step0 := by
      have heq : raw9938step0 = (fun i j => raw9938 (permutation349 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9938 permutation349 permutation11
    _ = injectiveMoment H node2889 := by rfl

def raw9939 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -3, 4]]

def raw9939step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9939 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9939 = injectiveMoment H node3222 := by
  calc
    injectiveMoment H raw9939 = injectiveMoment H raw9939step0 := by
      have heq : raw9939step0 = (fun i j => raw9939 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9939 permutation395 permutation9
    _ = injectiveMoment H node3222 := by rfl

def raw9940 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9940step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9940 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9940 = injectiveMoment H node3008 := by
  calc
    injectiveMoment H raw9940 = injectiveMoment H raw9940step0 := by
      have heq : raw9940step0 = (fun i j => raw9940 (permutation317 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9940 permutation317 permutation15
    _ = injectiveMoment H node3008 := by rfl

def raw9941 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9941step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical9941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9941 = injectiveMoment H node3190 := by
  calc
    injectiveMoment H raw9941 = injectiveMoment H raw9941step0 := by
      have heq : raw9941step0 = (fun i j => raw9941 (permutation273 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9941 permutation273 permutation16
    _ = injectiveMoment H node3190 := by rfl

def raw9942 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9942step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9942 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9942 = injectiveMoment H node3012 := by
  calc
    injectiveMoment H raw9942 = injectiveMoment H raw9942step0 := by
      have heq : raw9942step0 = (fun i j => raw9942 (permutation317 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9942 permutation317 permutation15
    _ = injectiveMoment H node3012 := by rfl

def raw9943 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9943step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw9943step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9943 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9943 = injectiveMoment H node3099 := by
  calc
    injectiveMoment H raw9943 = injectiveMoment H raw9943step0 := by
      have heq : raw9943step0 = -raw9943 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9943).symm
    injectiveMoment H raw9943step0 = injectiveMoment H raw9943step1 := by
      have heq : raw9943step1 = (fun i j => raw9943step0 (permutation367 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9943step0 permutation367 permutation29
    _ = injectiveMoment H node3099 := by rfl

def raw9944 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![-1, -2, 0, 3]]

def raw9944step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw9944step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical9944 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9944 = injectiveMoment H node3441 := by
  calc
    injectiveMoment H raw9944 = injectiveMoment H raw9944step0 := by
      have heq : raw9944step0 = -raw9944 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9944).symm
    injectiveMoment H raw9944step0 = injectiveMoment H raw9944step1 := by
      have heq : raw9944step1 = (fun i j => raw9944step0 (permutation163 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9944step0 permutation163 permutation23
    _ = injectiveMoment H node3441 := by rfl

def raw9945 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, -1, 4]]

def raw9945step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9945 = injectiveMoment H node2914 := by
  calc
    injectiveMoment H raw9945 = injectiveMoment H raw9945step0 := by
      have heq : raw9945step0 = (fun i j => raw9945 (permutation363 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9945 permutation363 permutation17
    _ = injectiveMoment H node2914 := by rfl

def raw9946 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, -1, 2]]

def raw9946step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9946 = injectiveMoment H node3079 := by
  calc
    injectiveMoment H raw9946 = injectiveMoment H raw9946step0 := by
      have heq : raw9946step0 = (fun i j => raw9946 (permutation349 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9946 permutation349 permutation11
    _ = injectiveMoment H node3079 := by rfl

def raw9947 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -2, 3]]

def raw9947step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

theorem canonical9947 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9947 = injectiveMoment H node3189 := by
  calc
    injectiveMoment H raw9947 = injectiveMoment H raw9947step0 := by
      have heq : raw9947step0 = (fun i j => raw9947 (permutation273 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9947 permutation273 permutation16
    _ = injectiveMoment H node3189 := by rfl

def raw9948 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -3, 2, 0], ![-1, 3, -3, 1]]

def raw9948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -3, 3], ![1, 2, -3], ![-1, 0, 1]]

def raw9948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![-1, -2, 3], ![1, 0, -1]]

def raw9948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical9948 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9948 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw9948 = injectiveMoment H raw9948step0 := by
      have heq : raw9948step0 = raw9948.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9948).symm
    injectiveMoment H raw9948step0 = injectiveMoment H raw9948step1 := by
      have heq : raw9948step1 = -raw9948step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9948step0).symm
    injectiveMoment H raw9948step1 = injectiveMoment H raw9948step2 := by
      have heq : raw9948step2 = (fun i j => raw9948step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9948step1 permutation21 permutation3
    _ = injectiveMoment H node269 := by rfl

def raw9949 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -2, 2, -1], ![-1, 2, -3, 2]]

def raw9949step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![-1, -1, 2]]

def raw9949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-1, -2, 3], ![1, 1, -2]]

def raw9949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical9949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9949 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw9949 = injectiveMoment H raw9949step0 := by
      have heq : raw9949step0 = raw9949.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9949).symm
    injectiveMoment H raw9949step0 = injectiveMoment H raw9949step1 := by
      have heq : raw9949step1 = -raw9949step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9949step0).symm
    injectiveMoment H raw9949step1 = injectiveMoment H raw9949step2 := by
      have heq : raw9949step2 = (fun i j => raw9949step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9949step1 permutation21 permutation3
    _ = injectiveMoment H node268 := by rfl

def raw9950 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![2, -3, 1, 0], ![-2, 3, -2, 1]]

def raw9950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![1, 1, -2], ![-1, 0, 1]]

def raw9950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![-1, -1, 2], ![1, 0, -1]]

def raw9950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical9950 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9950 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw9950 = injectiveMoment H raw9950step0 := by
      have heq : raw9950step0 = raw9950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9950).symm
    injectiveMoment H raw9950step0 = injectiveMoment H raw9950step1 := by
      have heq : raw9950step1 = -raw9950step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9950step0).symm
    injectiveMoment H raw9950step1 = injectiveMoment H raw9950step2 := by
      have heq : raw9950step2 = (fun i j => raw9950step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9950step1 permutation21 permutation3
    _ = injectiveMoment H node280 := by rfl

def raw9951 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![2, -2, 1, -1], ![-2, 2, -2, 2]]

def raw9951step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![-1, -1, 2]]

def raw9951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical9951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9951 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw9951 = injectiveMoment H raw9951step0 := by
      have heq : raw9951step0 = raw9951.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9951).symm
    injectiveMoment H raw9951step0 = injectiveMoment H raw9951step1 := by
      have heq : raw9951step1 = (fun i j => raw9951step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9951step0 permutation29 permutation3
    _ = injectiveMoment H node279 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
