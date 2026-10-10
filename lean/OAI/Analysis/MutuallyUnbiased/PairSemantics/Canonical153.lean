import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4896 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical4896 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4896 = injectiveMoment H node696 := by
  rfl

def raw4897 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4897 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4897 = injectiveMoment H node697 := by
  rfl

def raw4898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw4898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4898 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4898 = injectiveMoment H node697 := by
  calc
    injectiveMoment H raw4898 = injectiveMoment H raw4898step0 := by
      have heq : raw4898step0 = (fun i j => raw4898 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4898 permutation34 permutation3
    _ = injectiveMoment H node697 := by rfl

def raw4899 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4899 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4899 = injectiveMoment H node698 := by
  rfl

def raw4900 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical4900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4900 = injectiveMoment H node699 := by
  rfl

def raw4901 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![2, 0, -2]]

def raw4901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![0, -2, 2], ![-2, 0, 2]]

def raw4901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4901 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4901 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw4901 = injectiveMoment H raw4901step0 := by
      have heq : raw4901step0 = -raw4901 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4901).symm
    injectiveMoment H raw4901step0 = injectiveMoment H raw4901step1 := by
      have heq : raw4901step1 = (fun i j => raw4901step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4901step0 permutation32 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw4902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4902 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4902 = injectiveMoment H node700 := by
  rfl

def raw4903 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4903 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4903 = injectiveMoment H node220 := by
  rfl

def raw4904 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4904 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4904 = injectiveMoment H node221 := by
  rfl

def raw4905 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical4905 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4905 = injectiveMoment H node222 := by
  rfl

def raw4906 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical4906 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4906 = injectiveMoment H node223 := by
  rfl

def raw4907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]

def raw4907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical4907 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4907 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw4907 = injectiveMoment H raw4907step0 := by
      have heq : raw4907step0 = (fun i j => raw4907 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4907 permutation10 permutation3
    _ = injectiveMoment H node222 := by rfl

def raw4908 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]

def raw4908step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw4908step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4908 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4908 = injectiveMoment H raw4908step0 := by
      have heq : raw4908step0 = -raw4908 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4908).symm
    injectiveMoment H raw4908step0 = injectiveMoment H raw4908step1 := by
      have heq : raw4908step1 = (fun i j => raw4908step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4908step0 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

def raw4909 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4909 = injectiveMoment H node701 := by
  rfl

def raw4910 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical4910 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4910 = injectiveMoment H node702 := by
  rfl

def raw4911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw4911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw4911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4911 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4911 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4911 = injectiveMoment H raw4911step0 := by
      have hz : ∀ j, raw4911 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4911step0 = (fun i j => raw4911 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4911 permutation80 hz
    injectiveMoment H raw4911step0 = injectiveMoment H raw4911step1 := by
      have heq : raw4911step1 = (fun i j => raw4911step0 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4911step0 permutation17 permutation5
    _ = injectiveMoment H node210 := by rfl

def raw4912 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4912 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4912 = injectiveMoment H node704 := by
  rfl

def raw4913 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4913 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4913 = injectiveMoment H node705 := by
  rfl

def raw4914 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw4914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical4914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4914 = injectiveMoment H node667 := by
  calc
    injectiveMoment H raw4914 = injectiveMoment H raw4914step0 := by
      have heq : raw4914step0 = (fun i j => raw4914 (permutation72 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4914 permutation72 permutation5
    _ = injectiveMoment H node667 := by rfl

def raw4915 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]

def raw4915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 0, 2]]

def raw4915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4915 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4915 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4915 = injectiveMoment H raw4915step0 := by
      have heq : raw4915step0 = -raw4915 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4915).symm
    injectiveMoment H raw4915step0 = injectiveMoment H raw4915step1 := by
      have heq : raw4915step1 = (fun i j => raw4915step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4915step0 permutation32 permutation3
    _ = injectiveMoment H node203 := by rfl

def raw4916 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4916 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4916 = injectiveMoment H node706 := by
  rfl

def raw4917 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw4917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4917 = injectiveMoment H node706 := by
  calc
    injectiveMoment H raw4917 = injectiveMoment H raw4917step0 := by
      have heq : raw4917step0 = (fun i j => raw4917 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4917 permutation34 permutation3
    _ = injectiveMoment H node706 := by rfl

def raw4918 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4918 = injectiveMoment H node224 := by
  rfl

def raw4919 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw4919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical4919 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4919 = injectiveMoment H node699 := by
  calc
    injectiveMoment H raw4919 = injectiveMoment H raw4919step0 := by
      have heq : raw4919step0 = (fun i j => raw4919 (permutation39 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4919 permutation39 permutation4
    _ = injectiveMoment H node699 := by rfl

def raw4920 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 3, -3], ![2, -2, 0]]

def raw4920step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![0, -3, 3], ![-2, 2, 0]]

def raw4920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4920 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4920 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw4920 = injectiveMoment H raw4920step0 := by
      have heq : raw4920step0 = -raw4920 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4920).symm
    injectiveMoment H raw4920step0 = injectiveMoment H raw4920step1 := by
      have heq : raw4920step1 = (fun i j => raw4920step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4920step0 permutation30 permutation4
    _ = injectiveMoment H node198 := by rfl

def raw4921 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical4921 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4921 = injectiveMoment H node225 := by
  rfl

def raw4922 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical4922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4922 = injectiveMoment H node226 := by
  rfl

def raw4923 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw4923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4923 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4923 = injectiveMoment H raw4923step0 := by
      have heq : raw4923step0 = (fun i j => raw4923 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4923 permutation17 permutation5
    _ = injectiveMoment H node210 := by rfl

def raw4924 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw4924step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4924 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4924 = injectiveMoment H raw4924step0 := by
      have heq : raw4924step0 = (fun i j => raw4924 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4924 permutation19 permutation5
    _ = injectiveMoment H node210 := by rfl

def raw4925 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]

def raw4925step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw4925step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4925 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4925 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4925 = injectiveMoment H raw4925step0 := by
      have heq : raw4925step0 = -raw4925 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4925).symm
    injectiveMoment H raw4925step0 = injectiveMoment H raw4925step1 := by
      have heq : raw4925step1 = (fun i j => raw4925step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4925step0 permutation8 permutation3
    _ = injectiveMoment H node36 := by rfl

def raw4926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw4926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4926 = injectiveMoment H node701 := by
  calc
    injectiveMoment H raw4926 = injectiveMoment H raw4926step0 := by
      have heq : raw4926step0 = (fun i j => raw4926 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4926 permutation39 permutation3
    _ = injectiveMoment H node701 := by rfl

def raw4927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

def raw4927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical4927 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4927 = injectiveMoment H node702 := by
  calc
    injectiveMoment H raw4927 = injectiveMoment H raw4927step0 := by
      have heq : raw4927step0 = (fun i j => raw4927 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4927 permutation39 permutation3
    _ = injectiveMoment H node702 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
