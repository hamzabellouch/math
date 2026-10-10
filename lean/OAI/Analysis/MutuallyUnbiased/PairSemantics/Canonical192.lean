import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6144 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical6144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6144 = injectiveMoment H node2516 := by
  rfl

def raw6145 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6145step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem canonical6145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6145 = injectiveMoment H node2546 := by
  calc
    injectiveMoment H raw6145 = injectiveMoment H raw6145step0 := by
      have heq : raw6145step0 = (fun i j => raw6145 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6145 permutation36 permutation15
    _ = injectiveMoment H node2546 := by rfl

def raw6146 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw6146step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical6146 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6146 = injectiveMoment H node953 := by
  calc
    injectiveMoment H raw6146 = injectiveMoment H raw6146step0 := by
      have heq : raw6146step0 = (fun i j => raw6146 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6146 permutation10 permutation15
    _ = injectiveMoment H node953 := by rfl

def raw6147 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical6147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6147 = injectiveMoment H node2517 := by
  rfl

def raw6148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw6148step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6148 = injectiveMoment H node2545 := by
  calc
    injectiveMoment H raw6148 = injectiveMoment H raw6148step0 := by
      have heq : raw6148step0 = (fun i j => raw6148 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6148 permutation36 permutation15
    _ = injectiveMoment H node2545 := by rfl

def raw6149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical6149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6149 = injectiveMoment H node2518 := by
  rfl

def raw6150 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical6150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6150 = injectiveMoment H node2519 := by
  rfl

def raw6151 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw6151step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6151 = injectiveMoment H node2543 := by
  calc
    injectiveMoment H raw6151 = injectiveMoment H raw6151step0 := by
      have heq : raw6151step0 = (fun i j => raw6151 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6151 permutation36 permutation15
    _ = injectiveMoment H node2543 := by rfl

def raw6152 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw6152step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6152 = injectiveMoment H node2544 := by
  calc
    injectiveMoment H raw6152 = injectiveMoment H raw6152step0 := by
      have heq : raw6152step0 = (fun i j => raw6152 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6152 permutation36 permutation15
    _ = injectiveMoment H node2544 := by rfl

def raw6153 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6153step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -3, 2], ![0, -2, 2, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6153step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem canonical6153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6153 = injectiveMoment H node2020 := by
  calc
    injectiveMoment H raw6153 = injectiveMoment H raw6153step0 := by
      have heq : raw6153step0 = -raw6153 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6153).symm
    injectiveMoment H raw6153step0 = injectiveMoment H raw6153step1 := by
      have heq : raw6153step1 = (fun i j => raw6153step0 (permutation101 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6153step0 permutation101 permutation16
    _ = injectiveMoment H node2020 := by rfl

def raw6154 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6154step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -3, 2], ![0, -2, 1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw6154step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical6154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6154 = injectiveMoment H node2068 := by
  calc
    injectiveMoment H raw6154 = injectiveMoment H raw6154step0 := by
      have heq : raw6154step0 = -raw6154 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6154).symm
    injectiveMoment H raw6154step0 = injectiveMoment H raw6154step1 := by
      have heq : raw6154step1 = (fun i j => raw6154step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6154step0 permutation101 permutation15
    _ = injectiveMoment H node2068 := by rfl

def raw6155 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6155step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -3, 2], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6155step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem canonical6155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6155 = injectiveMoment H node2075 := by
  calc
    injectiveMoment H raw6155 = injectiveMoment H raw6155step0 := by
      have heq : raw6155step0 = -raw6155 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6155).symm
    injectiveMoment H raw6155step0 = injectiveMoment H raw6155step1 := by
      have heq : raw6155step1 = (fun i j => raw6155step0 (permutation101 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6155step0 permutation101 permutation16
    _ = injectiveMoment H node2075 := by rfl

def raw6156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw6156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -3, 2], ![-1, 1, 1, -1], ![-1, -2, 1, 2]]

def raw6156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical6156 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6156 = injectiveMoment H node509 := by
  calc
    injectiveMoment H raw6156 = injectiveMoment H raw6156step0 := by
      have heq : raw6156step0 = -raw6156 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6156).symm
    injectiveMoment H raw6156step0 = injectiveMoment H raw6156step1 := by
      have heq : raw6156step1 = (fun i j => raw6156step0 (permutation30 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6156step0 permutation30 permutation15
    _ = injectiveMoment H node509 := by rfl

def raw6157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw6157step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, -1, 2], ![-1, 3, 0, -2], ![3, -2, 0, -1]]

def raw6157step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 3, -2, -1], ![1, -1, -1, 1]]

theorem canonical6157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6157 = injectiveMoment H node1018 := by
  calc
    injectiveMoment H raw6157 = injectiveMoment H raw6157step0 := by
      have heq : raw6157step0 = raw6157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6157).symm
    injectiveMoment H raw6157step0 = injectiveMoment H raw6157step1 := by
      have heq : raw6157step1 = (fun i j => raw6157step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6157step0 permutation18 permutation21
    _ = injectiveMoment H node1018 := by rfl

def raw6158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw6158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical6158 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6158 = injectiveMoment H node948 := by
  calc
    injectiveMoment H raw6158 = injectiveMoment H raw6158step0 := by
      have heq : raw6158step0 = (fun i j => raw6158 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6158 permutation9 permutation15
    _ = injectiveMoment H node948 := by rfl

def raw6159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw6159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical6159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6159 = injectiveMoment H node949 := by
  calc
    injectiveMoment H raw6159 = injectiveMoment H raw6159step0 := by
      have heq : raw6159step0 = (fun i j => raw6159 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6159 permutation9 permutation15
    _ = injectiveMoment H node949 := by rfl

def raw6160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw6160step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical6160 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6160 = injectiveMoment H node950 := by
  calc
    injectiveMoment H raw6160 = injectiveMoment H raw6160step0 := by
      have heq : raw6160step0 = (fun i j => raw6160 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6160 permutation9 permutation15
    _ = injectiveMoment H node950 := by rfl

def raw6161 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical6161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6161 = injectiveMoment H node2520 := by
  rfl

def raw6162 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

theorem canonical6162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6162 = injectiveMoment H node2521 := by
  rfl

def raw6163 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw6163step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 1, -1], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw6163step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical6163 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6163 = injectiveMoment H node1736 := by
  calc
    injectiveMoment H raw6163 = injectiveMoment H raw6163step0 := by
      have heq : raw6163step0 = -raw6163 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6163).symm
    injectiveMoment H raw6163step0 = injectiveMoment H raw6163step1 := by
      have heq : raw6163step1 = (fun i j => raw6163step0 (permutation127 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6163step0 permutation127 permutation21
    _ = injectiveMoment H node1736 := by rfl

def raw6164 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical6164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6164 = injectiveMoment H node2522 := by
  rfl

def raw6165 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical6165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6165 = injectiveMoment H node2523 := by
  rfl

def raw6166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw6166step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 1, -1], ![0, -1, -1, 2], ![-2, 1, -1, 2]]

def raw6166step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical6166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6166 = injectiveMoment H node502 := by
  calc
    injectiveMoment H raw6166 = injectiveMoment H raw6166step0 := by
      have heq : raw6166step0 = -raw6166 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6166).symm
    injectiveMoment H raw6166step0 = injectiveMoment H raw6166step1 := by
      have heq : raw6166step1 = (fun i j => raw6166step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6166step0 permutation32 permutation11
    _ = injectiveMoment H node502 := by rfl

def raw6167 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical6167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6167 = injectiveMoment H node2524 := by
  rfl

def raw6168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw6168step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 1, -1], ![0, -1, -3, 4], ![-2, 1, 1, 0]]

def raw6168step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical6168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6168 = injectiveMoment H node712 := by
  calc
    injectiveMoment H raw6168 = injectiveMoment H raw6168step0 := by
      have heq : raw6168step0 = -raw6168 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6168).symm
    injectiveMoment H raw6168step0 = injectiveMoment H raw6168step1 := by
      have heq : raw6168step1 = (fun i j => raw6168step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6168step0 permutation32 permutation9
    _ = injectiveMoment H node712 := by rfl

def raw6169 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw6169step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, -1, 0, 2], ![3, 1, 0, -4]]

def raw6169step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6169 = injectiveMoment H node1341 := by
  calc
    injectiveMoment H raw6169 = injectiveMoment H raw6169step0 := by
      have heq : raw6169step0 = raw6169.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6169).symm
    injectiveMoment H raw6169step0 = injectiveMoment H raw6169step1 := by
      have heq : raw6169step1 = (fun i j => raw6169step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6169step0 permutation18 permutation23
    _ = injectiveMoment H node1341 := by rfl

def raw6170 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 1, -1, -1]]

theorem canonical6170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6170 = injectiveMoment H node925 := by
  rfl

def raw6171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw6171step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6171 = injectiveMoment H node986 := by
  calc
    injectiveMoment H raw6171 = injectiveMoment H raw6171step0 := by
      have heq : raw6171step0 = (fun i j => raw6171 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6171 permutation12 permutation15
    _ = injectiveMoment H node986 := by rfl

def raw6172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw6172step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical6172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6172 = injectiveMoment H node972 := by
  calc
    injectiveMoment H raw6172 = injectiveMoment H raw6172step0 := by
      have heq : raw6172step0 = (fun i j => raw6172 (permutation14 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6172 permutation14 permutation17
    _ = injectiveMoment H node972 := by rfl

def raw6173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw6173step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6173 = injectiveMoment H node986 := by
  calc
    injectiveMoment H raw6173 = injectiveMoment H raw6173step0 := by
      have heq : raw6173step0 = (fun i j => raw6173 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6173 permutation14 permutation15
    _ = injectiveMoment H node986 := by rfl

def raw6174 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, 1, 0, -2], ![1, -1, 2, -2]]

def raw6174step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 1, -1], ![-1, -1, 0, 2], ![-1, 1, -2, 2]]

def raw6174step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical6174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6174 = injectiveMoment H node502 := by
  calc
    injectiveMoment H raw6174 = injectiveMoment H raw6174step0 := by
      have heq : raw6174step0 = -raw6174 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6174).symm
    injectiveMoment H raw6174step0 = injectiveMoment H raw6174step1 := by
      have heq : raw6174step1 = (fun i j => raw6174step0 (permutation32 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6174step0 permutation32 permutation21
    _ = injectiveMoment H node502 := by rfl

def raw6175 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6175step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw6175step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical6175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6175 = injectiveMoment H node1768 := by
  calc
    injectiveMoment H raw6175 = injectiveMoment H raw6175step0 := by
      have heq : raw6175step0 = -raw6175 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6175).symm
    injectiveMoment H raw6175step0 = injectiveMoment H raw6175step1 := by
      have heq : raw6175step1 = (fun i j => raw6175step0 (permutation119 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6175step0 permutation119 permutation21
    _ = injectiveMoment H node1768 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
