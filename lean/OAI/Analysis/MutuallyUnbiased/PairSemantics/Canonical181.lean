import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw5792step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, 1, 0, -2], ![2, -2, -1, 1]]

def raw5792step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical5792 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5792 = injectiveMoment H node838 := by
  calc
    injectiveMoment H raw5792 = injectiveMoment H raw5792step0 := by
      have heq : raw5792step0 = raw5792.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5792).symm
    injectiveMoment H raw5792step0 = injectiveMoment H raw5792step1 := by
      have heq : raw5792step1 = (fun i j => raw5792step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5792step0 permutation28 permutation24
    _ = injectiveMoment H node838 := by rfl

def raw5793 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw5793step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0]]

def raw5793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical5793 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5793 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw5793 = injectiveMoment H raw5793step0 := by
      have heq : raw5793step0 = raw5793.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5793).symm
    injectiveMoment H raw5793step0 = injectiveMoment H raw5793step1 := by
      have heq : raw5793step1 = (fun i j => raw5793step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5793step0 permutation28 permutation6
    _ = injectiveMoment H node210 := by rfl

def raw5794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 2, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw5794step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical5794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5794 = injectiveMoment H node847 := by
  calc
    injectiveMoment H raw5794 = injectiveMoment H raw5794step0 := by
      have heq : raw5794step0 = (fun i j => raw5794 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5794 permutation11 permutation9
    _ = injectiveMoment H node847 := by rfl

def raw5795 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 2, -3], ![1, 1, -3, 1]]

def raw5795step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 2, -3], ![2, -3, 1]]

def raw5795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical5795 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5795 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw5795 = injectiveMoment H raw5795step0 := by
      have heq : raw5795step0 = raw5795.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5795).symm
    injectiveMoment H raw5795step0 = injectiveMoment H raw5795step1 := by
      have heq : raw5795step1 = (fun i j => raw5795step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5795step0 permutation27 permutation6
    _ = injectiveMoment H node109 := by rfl

def raw5796 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw5796step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -3, 2], ![2, 1, -3]]

def raw5796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical5796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5796 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw5796 = injectiveMoment H raw5796step0 := by
      have heq : raw5796step0 = raw5796.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5796).symm
    injectiveMoment H raw5796step0 = injectiveMoment H raw5796step1 := by
      have heq : raw5796step1 = (fun i j => raw5796step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5796step0 permutation22 permutation5
    _ = injectiveMoment H node107 := by rfl

def raw5797 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw5797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2]]

def raw5797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -2, 0], ![-1, 2, -1], ![-2, 0, 2]]

def raw5797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5797 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5797 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5797 = injectiveMoment H raw5797step0 := by
      have heq : raw5797step0 = raw5797.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5797).symm
    injectiveMoment H raw5797step0 = injectiveMoment H raw5797step1 := by
      have heq : raw5797step1 = -raw5797step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5797step0).symm
    injectiveMoment H raw5797step1 = injectiveMoment H raw5797step2 := by
      have heq : raw5797step2 = (fun i j => raw5797step1 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5797step1 permutation16 permutation6
    _ = injectiveMoment H node203 := by rfl

def raw5798 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5798step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1]]

def raw5798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5798 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw5798 = injectiveMoment H raw5798step0 := by
      have heq : raw5798step0 = raw5798.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5798).symm
    injectiveMoment H raw5798step0 = injectiveMoment H raw5798step1 := by
      have heq : raw5798step1 = (fun i j => raw5798step0 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5798step0 permutation32 permutation8
    _ = injectiveMoment H node284 := by rfl

def raw5799 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0]]

def raw5799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5799 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw5799 = injectiveMoment H raw5799step0 := by
      have heq : raw5799step0 = raw5799.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5799).symm
    injectiveMoment H raw5799step0 = injectiveMoment H raw5799step1 := by
      have heq : raw5799step1 = (fun i j => raw5799step0 (permutation26 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5799step0 permutation26 permutation8
    _ = injectiveMoment H node291 := by rfl

def raw5800 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw5800step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 1, -2], ![2, -3, 1]]

def raw5800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5800 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5800 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw5800 = injectiveMoment H raw5800step0 := by
      have heq : raw5800step0 = raw5800.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5800).symm
    injectiveMoment H raw5800step0 = injectiveMoment H raw5800step1 := by
      have heq : raw5800step1 = (fun i j => raw5800step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5800step0 permutation23 permutation7
    _ = injectiveMoment H node226 := by rfl

def raw5801 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def raw5801step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 2, -3], ![2, -4, 2]]

def raw5801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

theorem canonical5801 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5801 = injectiveMoment H node102 := by
  calc
    injectiveMoment H raw5801 = injectiveMoment H raw5801step0 := by
      have heq : raw5801step0 = raw5801.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5801).symm
    injectiveMoment H raw5801step0 = injectiveMoment H raw5801step1 := by
      have heq : raw5801step1 = (fun i j => raw5801step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5801step0 permutation23 permutation7
    _ = injectiveMoment H node102 := by rfl

def raw5802 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 0, -3, 2], ![0, 2, 2, -4]]

def raw5802step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2], ![2, 2, -4]]

def raw5802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

theorem canonical5802 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5802 = injectiveMoment H node102 := by
  calc
    injectiveMoment H raw5802 = injectiveMoment H raw5802step0 := by
      have heq : raw5802step0 = raw5802.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5802).symm
    injectiveMoment H raw5802step0 = injectiveMoment H raw5802step1 := by
      have heq : raw5802step1 = (fun i j => raw5802step0 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5802step0 permutation23 permutation5
    _ = injectiveMoment H node102 := by rfl

def raw5803 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 0, -2, 1], ![0, 2, 1, -3]]

def raw5803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 1, -3]]

def raw5803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5803 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw5803 = injectiveMoment H raw5803step0 := by
      have heq : raw5803step0 = raw5803.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5803).symm
    injectiveMoment H raw5803step0 = injectiveMoment H raw5803step1 := by
      have heq : raw5803step1 = (fun i j => raw5803step0 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5803step0 permutation23 permutation5
    _ = injectiveMoment H node226 := by rfl

def raw5804 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 0, 2, -3], ![0, 2, -3, 1]]

def raw5804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 2, -3], ![2, -3, 1]]

def raw5804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical5804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5804 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw5804 = injectiveMoment H raw5804step0 := by
      have heq : raw5804step0 = raw5804.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5804).symm
    injectiveMoment H raw5804step0 = injectiveMoment H raw5804step1 := by
      have heq : raw5804step1 = (fun i j => raw5804step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5804step0 permutation22 permutation7
    _ = injectiveMoment H node107 := by rfl

def raw5805 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 1, -3, 1], ![0, 1, 2, -3]]

def raw5805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2], ![2, 1, -3]]

def raw5805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical5805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5805 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw5805 = injectiveMoment H raw5805step0 := by
      have heq : raw5805step0 = raw5805.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5805).symm
    injectiveMoment H raw5805step0 = injectiveMoment H raw5805step1 := by
      have heq : raw5805step1 = (fun i j => raw5805step0 (permutation27 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5805step0 permutation27 permutation8
    _ = injectiveMoment H node109 := by rfl

def raw5806 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 1, -2, 0], ![0, 1, 1, -2]]

def raw5806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2]]

def raw5806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical5806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5806 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw5806 = injectiveMoment H raw5806step0 := by
      have heq : raw5806step0 = raw5806.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5806).symm
    injectiveMoment H raw5806step0 = injectiveMoment H raw5806step1 := by
      have heq : raw5806step1 = (fun i j => raw5806step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5806step0 permutation28 permutation8
    _ = injectiveMoment H node210 := by rfl

def raw5807 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-3, 1, 0, 2], ![4, 1, -2, -3]]

def raw5807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-2, 1, 1], ![2, 0, -2], ![1, 2, -3]]

def raw5807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical5807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5807 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw5807 = injectiveMoment H raw5807step0 := by
      have heq : raw5807step0 = raw5807.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5807).symm
    injectiveMoment H raw5807step0 = injectiveMoment H raw5807step1 := by
      have heq : raw5807step1 = (fun i j => raw5807step0 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5807step0 permutation11 permutation5
    _ = injectiveMoment H node84 := by rfl

def raw5808 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-3, 2, -1, 2], ![4, 0, -1, -3]]

def raw5808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-2, 2, 0], ![2, -1, -1], ![1, 2, -3]]

def raw5808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical5808 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5808 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw5808 = injectiveMoment H raw5808step0 := by
      have heq : raw5808step0 = raw5808.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5808).symm
    injectiveMoment H raw5808step0 = injectiveMoment H raw5808step1 := by
      have heq : raw5808step1 = (fun i j => raw5808step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5808step0 permutation16 permutation4
    _ = injectiveMoment H node191 := by rfl

def raw5809 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-3, 2, 0, 1], ![4, 0, -2, -2]]

def raw5809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-2, 2, 0], ![2, 0, -2], ![1, 1, -2]]

def raw5809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical5809 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5809 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw5809 = injectiveMoment H raw5809step0 := by
      have heq : raw5809step0 = raw5809.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5809).symm
    injectiveMoment H raw5809step0 = injectiveMoment H raw5809step1 := by
      have heq : raw5809step1 = (fun i j => raw5809step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5809step0 permutation12 permutation5
    _ = injectiveMoment H node85 := by rfl

def raw5810 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-3, 3, -1, 1], ![4, -1, -1, -2]]

def raw5810step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-2, 3, -1], ![2, -1, -1], ![1, 1, -2]]

def raw5810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical5810 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5810 = injectiveMoment H node161 := by
  calc
    injectiveMoment H raw5810 = injectiveMoment H raw5810step0 := by
      have heq : raw5810step0 = raw5810.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5810).symm
    injectiveMoment H raw5810step0 = injectiveMoment H raw5810step1 := by
      have heq : raw5810step1 = (fun i j => raw5810step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5810step0 permutation16 permutation4
    _ = injectiveMoment H node161 := by rfl

def raw5811 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 1, -1, 2], ![3, 1, -1, -3]]

def raw5811step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 1, 1], ![2, -1, -1], ![1, 2, -3]]

def raw5811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical5811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5811 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw5811 = injectiveMoment H raw5811step0 := by
      have heq : raw5811step0 = raw5811.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5811).symm
    injectiveMoment H raw5811step0 = injectiveMoment H raw5811step1 := by
      have heq : raw5811step1 = (fun i j => raw5811step0 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5811step0 permutation11 permutation5
    _ = injectiveMoment H node159 := by rfl

def raw5812 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 1, 2, -1], ![3, 1, -4, 0]]

def raw5812step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 1, 1], ![2, 2, -4], ![1, -1, 0]]

def raw5812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, -2, 4], ![-1, 1, 0]]

def raw5812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

theorem canonical5812 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5812 = injectiveMoment H node132 := by
  calc
    injectiveMoment H raw5812 = injectiveMoment H raw5812step0 := by
      have heq : raw5812step0 = raw5812.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5812).symm
    injectiveMoment H raw5812step0 = injectiveMoment H raw5812step1 := by
      have heq : raw5812step1 = -raw5812step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5812step0).symm
    injectiveMoment H raw5812step1 = injectiveMoment H raw5812step2 := by
      have heq : raw5812step2 = (fun i j => raw5812step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5812step1 permutation25 permutation3
    _ = injectiveMoment H node132 := by rfl

def raw5813 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 2, -1, 1], ![3, 0, -1, -2]]

def raw5813step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 2, 0], ![2, -1, -1], ![1, 1, -2]]

def raw5813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]

def raw5813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical5813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5813 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw5813 = injectiveMoment H raw5813step0 := by
      have heq : raw5813step0 = raw5813.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5813).symm
    injectiveMoment H raw5813step0 = injectiveMoment H raw5813step1 := by
      have heq : raw5813step1 = -raw5813step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5813step0).symm
    injectiveMoment H raw5813step1 = injectiveMoment H raw5813step2 := by
      have heq : raw5813step2 = (fun i j => raw5813step1 (permutation9 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5813step1 permutation9 permutation7
    _ = injectiveMoment H node111 := by rfl

def raw5814 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 2, 1, -1], ![3, 0, -3, 0]]

def raw5814step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 2, 0], ![2, 1, -3], ![1, -1, 0]]

def raw5814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical5814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5814 = injectiveMoment H node105 := by
  calc
    injectiveMoment H raw5814 = injectiveMoment H raw5814step0 := by
      have heq : raw5814step0 = raw5814.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5814).symm
    injectiveMoment H raw5814step0 = injectiveMoment H raw5814step1 := by
      have heq : raw5814step1 = (fun i j => raw5814step0 (permutation26 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5814step0 permutation26 permutation8
    _ = injectiveMoment H node105 := by rfl

def raw5815 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 2, 2, -2], ![3, 0, -4, 1]]

def raw5815step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 2, 0], ![2, 2, -4], ![1, -2, 1]]

def raw5815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, -2, 4], ![-1, 2, -1]]

def raw5815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical5815 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5815 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw5815 = injectiveMoment H raw5815step0 := by
      have heq : raw5815step0 = raw5815.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5815).symm
    injectiveMoment H raw5815step0 = injectiveMoment H raw5815step1 := by
      have heq : raw5815step1 = -raw5815step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5815step0).symm
    injectiveMoment H raw5815step1 = injectiveMoment H raw5815step2 := by
      have heq : raw5815step2 = (fun i j => raw5815step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5815step1 permutation25 permutation3
    _ = injectiveMoment H node135 := by rfl

def raw5816 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 4, 0, -2], ![3, -2, -2, 1]]

def raw5816step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 4, -2], ![2, 0, -2], ![1, -2, 1]]

def raw5816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical5816 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5816 = injectiveMoment H node136 := by
  calc
    injectiveMoment H raw5816 = injectiveMoment H raw5816step0 := by
      have heq : raw5816step0 = raw5816.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5816).symm
    injectiveMoment H raw5816step0 = injectiveMoment H raw5816step1 := by
      have heq : raw5816step1 = (fun i j => raw5816step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5816step0 permutation16 permutation4
    _ = injectiveMoment H node136 := by rfl

def raw5817 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, 0, 3, -2], ![2, 2, -5, 1]]

def raw5817step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![2, 3, -5], ![1, -2, 1]]

def raw5817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, -3, 5], ![-1, 2, -1]]

def raw5817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical5817 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5817 = injectiveMoment H node74 := by
  calc
    injectiveMoment H raw5817 = injectiveMoment H raw5817step0 := by
      have heq : raw5817step0 = raw5817.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5817).symm
    injectiveMoment H raw5817step0 = injectiveMoment H raw5817step1 := by
      have heq : raw5817step1 = -raw5817step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5817step0).symm
    injectiveMoment H raw5817step1 = injectiveMoment H raw5817step2 := by
      have heq : raw5817step2 = (fun i j => raw5817step1 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5817step1 permutation23 permutation5
    _ = injectiveMoment H node74 := by rfl

def raw5818 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, 1, 2, -2], ![2, 1, -4, 1]]

def raw5818step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 1, 1], ![2, 2, -4], ![1, -2, 1]]

def raw5818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, -2, 4], ![-1, 2, -1]]

def raw5818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical5818 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5818 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw5818 = injectiveMoment H raw5818step0 := by
      have heq : raw5818step0 = raw5818.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5818).symm
    injectiveMoment H raw5818step0 = injectiveMoment H raw5818step1 := by
      have heq : raw5818step1 = -raw5818step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5818step0).symm
    injectiveMoment H raw5818step1 = injectiveMoment H raw5818step2 := by
      have heq : raw5818step2 = (fun i j => raw5818step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5818step1 permutation25 permutation3
    _ = injectiveMoment H node134 := by rfl

def raw5819 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, 2, 1, -2], ![2, 0, -3, 1]]

def raw5819step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, 1, -3], ![1, -2, 1]]

def raw5819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical5819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5819 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw5819 = injectiveMoment H raw5819step0 := by
      have heq : raw5819step0 = raw5819.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5819).symm
    injectiveMoment H raw5819step0 = injectiveMoment H raw5819step1 := by
      have heq : raw5819step1 = (fun i j => raw5819step0 (permutation24 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5819step0 permutation24 permutation8
    _ = injectiveMoment H node111 := by rfl

def raw5820 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, 3, -3, 1], ![2, -1, 1, -2]]

def raw5820step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![2, -3, 1], ![1, 1, -2]]

def raw5820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical5820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5820 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw5820 = injectiveMoment H raw5820step0 := by
      have heq : raw5820step0 = raw5820.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5820).symm
    injectiveMoment H raw5820step0 = injectiveMoment H raw5820step1 := by
      have heq : raw5820step1 = (fun i j => raw5820step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5820step0 permutation16 permutation4
    _ = injectiveMoment H node159 := by rfl

def raw5821 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, -1, 2, -1], ![1, 3, -4, 0]]

def raw5821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![2, 2, -4], ![1, -1, 0]]

def raw5821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 1, -3], ![-2, -2, 4], ![-1, 1, 0]]

def raw5821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5821 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5821 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw5821 = injectiveMoment H raw5821step0 := by
      have heq : raw5821step0 = raw5821.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5821).symm
    injectiveMoment H raw5821step0 = injectiveMoment H raw5821step1 := by
      have heq : raw5821step1 = -raw5821step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5821step0).symm
    injectiveMoment H raw5821step1 = injectiveMoment H raw5821step2 := by
      have heq : raw5821step2 = (fun i j => raw5821step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5821step1 permutation22 permutation5
    _ = injectiveMoment H node149 := by rfl

def raw5822 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem canonical5822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5822 = injectiveMoment H node853 := by
  rfl

def raw5823 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical5823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5823 = injectiveMoment H node854 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
