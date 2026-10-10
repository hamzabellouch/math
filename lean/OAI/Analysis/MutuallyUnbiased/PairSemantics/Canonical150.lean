import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4800 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -3, 3]]

def raw4800step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw4800step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -1, -2, 3], ![-1, 1, 3, -3]]

def raw4800step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, 3, -3]]

theorem canonical4800 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4800 = injectiveMoment H node1196 := by
  calc
    injectiveMoment H raw4800 = injectiveMoment H raw4800step0 := by
      have heq : raw4800step0 = raw4800.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4800).symm
    injectiveMoment H raw4800step0 = injectiveMoment H raw4800step1 := by
      have heq : raw4800step1 = -raw4800step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4800step0).symm
    injectiveMoment H raw4800step1 = injectiveMoment H raw4800step2 := by
      have heq : raw4800step2 = (fun i j => raw4800step1 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4800step1 permutation23 permutation15
    _ = injectiveMoment H node1196 := by rfl

def raw4801 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -2, -2, 3], ![1, 1, 1, -3]]

def raw4801step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw4801step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![-1, 1, -3, 3]]

def raw4801step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem canonical4801 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4801 = injectiveMoment H node1239 := by
  calc
    injectiveMoment H raw4801 = injectiveMoment H raw4801step0 := by
      have heq : raw4801step0 = raw4801.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4801).symm
    injectiveMoment H raw4801step0 = injectiveMoment H raw4801step1 := by
      have heq : raw4801step1 = -raw4801step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4801step0).symm
    injectiveMoment H raw4801step1 = injectiveMoment H raw4801step2 := by
      have heq : raw4801step2 = (fun i j => raw4801step1 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4801step1 permutation23 permutation16
    _ = injectiveMoment H node1239 := by rfl

def raw4802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw4802step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw4802step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![-1, 1, 1, -1]]

def raw4802step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical4802 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4802 = injectiveMoment H node1208 := by
  calc
    injectiveMoment H raw4802 = injectiveMoment H raw4802step0 := by
      have heq : raw4802step0 = raw4802.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4802).symm
    injectiveMoment H raw4802step0 = injectiveMoment H raw4802step1 := by
      have heq : raw4802step1 = -raw4802step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4802step0).symm
    injectiveMoment H raw4802step1 = injectiveMoment H raw4802step2 := by
      have heq : raw4802step2 = (fun i j => raw4802step1 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4802step1 permutation23 permutation15
    _ = injectiveMoment H node1208 := by rfl

def raw4803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 0, 2, -3]]

def raw4803step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, 1, -3, 2], ![1, -1, 3, -3]]

def raw4803step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![0, -1, 3, -2], ![-1, 1, -3, 3]]

def raw4803step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem canonical4803 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4803 = injectiveMoment H node1200 := by
  calc
    injectiveMoment H raw4803 = injectiveMoment H raw4803step0 := by
      have heq : raw4803step0 = raw4803.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4803).symm
    injectiveMoment H raw4803step0 = injectiveMoment H raw4803step1 := by
      have heq : raw4803step1 = -raw4803step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4803step0).symm
    injectiveMoment H raw4803step1 = injectiveMoment H raw4803step2 := by
      have heq : raw4803step2 = (fun i j => raw4803step1 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4803step1 permutation23 permutation16
    _ = injectiveMoment H node1200 := by rfl

def raw4804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 0, -3, 2]]

def raw4804step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4804step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![0, -1, -2, 3], ![-1, 1, 2, -2]]

def raw4804step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical4804 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4804 = injectiveMoment H node1204 := by
  calc
    injectiveMoment H raw4804 = injectiveMoment H raw4804step0 := by
      have heq : raw4804step0 = raw4804.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4804).symm
    injectiveMoment H raw4804step0 = injectiveMoment H raw4804step1 := by
      have heq : raw4804step1 = -raw4804step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4804step0).symm
    injectiveMoment H raw4804step1 = injectiveMoment H raw4804step2 := by
      have heq : raw4804step2 = (fun i j => raw4804step1 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4804step1 permutation23 permutation15
    _ = injectiveMoment H node1204 := by rfl

def raw4805 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4805step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical4805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4805 = injectiveMoment H node2805 := by
  calc
    injectiveMoment H raw4805 = injectiveMoment H raw4805step0 := by
      have heq : raw4805step0 = (fun i j => raw4805 (permutation121 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4805 permutation121 permutation17
    _ = injectiveMoment H node2805 := by rfl

def raw4806 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4806step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

theorem canonical4806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4806 = injectiveMoment H node2289 := by
  calc
    injectiveMoment H raw4806 = injectiveMoment H raw4806step0 := by
      have heq : raw4806step0 = (fun i j => raw4806 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4806 permutation39 permutation9
    _ = injectiveMoment H node2289 := by rfl

def raw4807 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4807step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

theorem canonical4807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4807 = injectiveMoment H node2290 := by
  calc
    injectiveMoment H raw4807 = injectiveMoment H raw4807step0 := by
      have heq : raw4807step0 = (fun i j => raw4807 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4807 permutation39 permutation9
    _ = injectiveMoment H node2290 := by rfl

def raw4808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -3, 2], ![2, -2, 1, -1]]

def raw4808step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, -3, 1], ![1, -2, 2, -1]]

def raw4808step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -2, 3, -1], ![-1, 2, -2, 1]]

def raw4808step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem canonical4808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4808 = injectiveMoment H node588 := by
  calc
    injectiveMoment H raw4808 = injectiveMoment H raw4808step0 := by
      have heq : raw4808step0 = raw4808.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4808).symm
    injectiveMoment H raw4808step0 = injectiveMoment H raw4808step1 := by
      have heq : raw4808step1 = -raw4808step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4808step0).symm
    injectiveMoment H raw4808step1 = injectiveMoment H raw4808step2 := by
      have heq : raw4808step2 = (fun i j => raw4808step1 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4808step1 permutation23 permutation16
    _ = injectiveMoment H node588 := by rfl

def raw4809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4809step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4809step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical4809 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4809 = injectiveMoment H node2013 := by
  calc
    injectiveMoment H raw4809 = injectiveMoment H raw4809step0 := by
      have heq : raw4809step0 = -raw4809 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4809).symm
    injectiveMoment H raw4809step0 = injectiveMoment H raw4809step1 := by
      have heq : raw4809step1 = (fun i j => raw4809step0 (permutation72 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4809step0 permutation72 permutation21
    _ = injectiveMoment H node2013 := by rfl

def raw4810 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw4810step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-2, 2, 0, 0]]

def raw4810step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical4810 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4810 = injectiveMoment H node606 := by
  calc
    injectiveMoment H raw4810 = injectiveMoment H raw4810step0 := by
      have heq : raw4810step0 = -raw4810 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4810).symm
    injectiveMoment H raw4810step0 = injectiveMoment H raw4810step1 := by
      have heq : raw4810step1 = (fun i j => raw4810step0 (permutation30 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4810step0 permutation30 permutation12
    _ = injectiveMoment H node606 := by rfl

def raw4811 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4811step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, 0, 1, 0]]

def raw4811step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical4811 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4811 = injectiveMoment H node2023 := by
  calc
    injectiveMoment H raw4811 = injectiveMoment H raw4811step0 := by
      have heq : raw4811step0 = -raw4811 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4811).symm
    injectiveMoment H raw4811step0 = injectiveMoment H raw4811step1 := by
      have heq : raw4811step1 = (fun i j => raw4811step0 (permutation69 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4811step0 permutation69 permutation21
    _ = injectiveMoment H node2023 := by rfl

def raw4812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

theorem canonical4812 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4812 = injectiveMoment H node2292 := by
  rfl

def raw4813 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4813step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical4813 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4813 = injectiveMoment H node2018 := by
  calc
    injectiveMoment H raw4813 = injectiveMoment H raw4813step0 := by
      have heq : raw4813step0 = (fun i j => raw4813 (permutation77 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4813 permutation77 permutation29
    _ = injectiveMoment H node2018 := by rfl

def raw4814 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4814step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -2, 0, 1]]

def raw4814step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -2, 1, 1], ![-1, 2, 0, -1]]

def raw4814step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical4814 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4814 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw4814 = injectiveMoment H raw4814step0 := by
      have heq : raw4814step0 = raw4814.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4814).symm
    injectiveMoment H raw4814step0 = injectiveMoment H raw4814step1 := by
      have heq : raw4814step1 = -raw4814step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4814step0).symm
    injectiveMoment H raw4814step1 = injectiveMoment H raw4814step2 := by
      have heq : raw4814step2 = (fun i j => raw4814step1 (permutation19 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4814step1 permutation19 permutation21
    _ = injectiveMoment H node1010 := by rfl

def raw4815 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4815step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical4815 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4815 = injectiveMoment H node1744 := by
  calc
    injectiveMoment H raw4815 = injectiveMoment H raw4815step0 := by
      have heq : raw4815step0 = (fun i j => raw4815 (permutation123 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4815 permutation123 permutation23
    _ = injectiveMoment H node1744 := by rfl

def raw4816 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4816step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw4816step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical4816 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4816 = injectiveMoment H node831 := by
  calc
    injectiveMoment H raw4816 = injectiveMoment H raw4816step0 := by
      have heq : raw4816step0 = raw4816.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4816).symm
    injectiveMoment H raw4816step0 = injectiveMoment H raw4816step1 := by
      have heq : raw4816step1 = (fun i j => raw4816step0 (permutation28 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4816step0 permutation28 permutation23
    _ = injectiveMoment H node831 := by rfl

def raw4817 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def raw4817step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw4817step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

theorem canonical4817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4817 = injectiveMoment H node405 := by
  calc
    injectiveMoment H raw4817 = injectiveMoment H raw4817step0 := by
      have heq : raw4817step0 = raw4817.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4817).symm
    injectiveMoment H raw4817step0 = injectiveMoment H raw4817step1 := by
      have heq : raw4817step1 = (fun i j => raw4817step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4817step0 permutation27 permutation17
    _ = injectiveMoment H node405 := by rfl

def raw4818 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -2, -2, 3], ![1, 1, 0, -2]]

def raw4818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical4818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4818 = injectiveMoment H node408 := by
  calc
    injectiveMoment H raw4818 = injectiveMoment H raw4818step0 := by
      have heq : raw4818step0 = (fun i j => raw4818 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4818 permutation22 permutation23
    _ = injectiveMoment H node408 := by rfl

def raw4819 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 0, 1, -2]]

def raw4819step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 0, 1]]

theorem canonical4819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4819 = injectiveMoment H node1329 := by
  calc
    injectiveMoment H raw4819 = injectiveMoment H raw4819step0 := by
      have heq : raw4819step0 = (fun i j => raw4819 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4819 permutation24 permutation15
    _ = injectiveMoment H node1329 := by rfl

def raw4820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw4820step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical4820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4820 = injectiveMoment H node840 := by
  calc
    injectiveMoment H raw4820 = injectiveMoment H raw4820step0 := by
      have heq : raw4820step0 = (fun i j => raw4820 (permutation26 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4820 permutation26 permutation17
    _ = injectiveMoment H node840 := by rfl

def raw4821 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, 0, -3, 2], ![1, -1, 1, -1]]

def raw4821step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical4821 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4821 = injectiveMoment H node1347 := by
  calc
    injectiveMoment H raw4821 = injectiveMoment H raw4821step0 := by
      have heq : raw4821step0 = (fun i j => raw4821 (permutation30 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4821 permutation30 permutation16
    _ = injectiveMoment H node1347 := by rfl

def raw4822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4822step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical4822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4822 = injectiveMoment H node2849 := by
  calc
    injectiveMoment H raw4822 = injectiveMoment H raw4822step0 := by
      have heq : raw4822step0 = (fun i j => raw4822 (permutation113 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4822 permutation113 permutation16
    _ = injectiveMoment H node2849 := by rfl

def raw4823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem canonical4823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4823 = injectiveMoment H node2293 := by
  rfl

def raw4824 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4824step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 3, -1, -2], ![1, -3, 0, 2]]

def raw4824step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -3, 1, 2], ![-1, 3, 0, -2]]

def raw4824step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -3, 2]]

theorem canonical4824 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4824 = injectiveMoment H node1017 := by
  calc
    injectiveMoment H raw4824 = injectiveMoment H raw4824step0 := by
      have heq : raw4824step0 = raw4824.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4824).symm
    injectiveMoment H raw4824step0 = injectiveMoment H raw4824step1 := by
      have heq : raw4824step1 = -raw4824step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4824step0).symm
    injectiveMoment H raw4824step1 = injectiveMoment H raw4824step2 := by
      have heq : raw4824step2 = (fun i j => raw4824step1 (permutation19 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4824step1 permutation19 permutation21
    _ = injectiveMoment H node1017 := by rfl

def raw4825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4825step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 3, 0, -3], ![1, -3, -1, 3]]

def raw4825step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -3, 0, 3], ![-1, 3, 1, -3]]

def raw4825step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 2, 0, -2], ![1, -1, 3, -3]]

theorem canonical4825 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4825 = injectiveMoment H node1025 := by
  calc
    injectiveMoment H raw4825 = injectiveMoment H raw4825step0 := by
      have heq : raw4825step0 = raw4825.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4825).symm
    injectiveMoment H raw4825step0 = injectiveMoment H raw4825step1 := by
      have heq : raw4825step1 = -raw4825step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4825step0).symm
    injectiveMoment H raw4825step1 = injectiveMoment H raw4825step2 := by
      have heq : raw4825step2 = (fun i j => raw4825step1 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4825step1 permutation17 permutation21
    _ = injectiveMoment H node1025 := by rfl

def raw4826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw4826step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, 3, -2, -1], ![1, -3, 2, 0]]

def raw4826step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical4826 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4826 = injectiveMoment H node1231 := by
  calc
    injectiveMoment H raw4826 = injectiveMoment H raw4826step0 := by
      have heq : raw4826step0 = raw4826.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4826).symm
    injectiveMoment H raw4826step0 = injectiveMoment H raw4826step1 := by
      have heq : raw4826step1 = (fun i j => raw4826step0 (permutation24 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4826step0 permutation24 permutation28
    _ = injectiveMoment H node1231 := by rfl

def raw4827 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw4827step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

theorem canonical4827 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4827 = injectiveMoment H node1352 := by
  calc
    injectiveMoment H raw4827 = injectiveMoment H raw4827step0 := by
      have heq : raw4827step0 = (fun i j => raw4827 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4827 permutation24 permutation15
    _ = injectiveMoment H node1352 := by rfl

def raw4828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw4828step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical4828 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4828 = injectiveMoment H node1355 := by
  calc
    injectiveMoment H raw4828 = injectiveMoment H raw4828step0 := by
      have heq : raw4828step0 = (fun i j => raw4828 (permutation24 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4828 permutation24 permutation16
    _ = injectiveMoment H node1355 := by rfl

def raw4829 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, 0, -3, 2], ![1, -1, 0, 0]]

def raw4829step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical4829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4829 = injectiveMoment H node1355 := by
  calc
    injectiveMoment H raw4829 = injectiveMoment H raw4829step0 := by
      have heq : raw4829step0 = (fun i j => raw4829 (permutation30 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4829 permutation30 permutation16
    _ = injectiveMoment H node1355 := by rfl

def raw4830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![0, 0, 2, -2], ![2, -2, 1, -1]]

def raw4830step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 1, 0, -2], ![0, -3, 2, 1], ![1, 2, -2, -1]]

def raw4830step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, -1, 0, 2], ![0, 3, -2, -1], ![-1, -2, 2, 1]]

def raw4830step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem canonical4830 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4830 = injectiveMoment H node588 := by
  calc
    injectiveMoment H raw4830 = injectiveMoment H raw4830step0 := by
      have heq : raw4830step0 = raw4830.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4830).symm
    injectiveMoment H raw4830step0 = injectiveMoment H raw4830step1 := by
      have heq : raw4830step1 = -raw4830step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4830step0).symm
    injectiveMoment H raw4830step1 = injectiveMoment H raw4830step2 := by
      have heq : raw4830step2 = (fun i j => raw4830step1 (permutation23 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4830step1 permutation23 permutation22
    _ = injectiveMoment H node588 := by rfl

def raw4831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -3, 0, 3], ![1, 2, 1, -4]]

def raw4831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical4831 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4831 = injectiveMoment H node692 := by
  calc
    injectiveMoment H raw4831 = injectiveMoment H raw4831step0 := by
      have heq : raw4831step0 = raw4831.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4831).symm
    injectiveMoment H raw4831step0 = injectiveMoment H raw4831step1 := by
      have heq : raw4831step1 = (fun i j => raw4831step0 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4831step0 permutation11 permutation11
    _ = injectiveMoment H node692 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
