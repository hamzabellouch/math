import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6112 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw6112step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-2, -1, 3], ![4, -1, -3]]

def raw6112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![2, 1, -3], ![-4, 1, 3]]

def raw6112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical6112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6112 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw6112 = injectiveMoment H raw6112step0 := by
      have heq : raw6112step0 = raw6112.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6112).symm
    injectiveMoment H raw6112step0 = injectiveMoment H raw6112step1 := by
      have heq : raw6112step1 = -raw6112step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6112step0).symm
    injectiveMoment H raw6112step1 = injectiveMoment H raw6112step2 := by
      have heq : raw6112step2 = (fun i j => raw6112step1 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6112step1 permutation15 permutation6
    _ = injectiveMoment H node228 := by rfl

def raw6113 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw6113step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-2, 0, 2], ![4, -2, -2]]

def raw6113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical6113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6113 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw6113 = injectiveMoment H raw6113step0 := by
      have heq : raw6113step0 = raw6113.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6113).symm
    injectiveMoment H raw6113step0 = injectiveMoment H raw6113step1 := by
      have heq : raw6113step1 = (fun i j => raw6113step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6113step0 permutation28 permutation6
    _ = injectiveMoment H node146 := by rfl

def raw6114 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw6114step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-2, 1, 1], ![4, -3, -1]]

def raw6114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6114 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw6114 = injectiveMoment H raw6114step0 := by
      have heq : raw6114step0 = raw6114.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6114).symm
    injectiveMoment H raw6114step0 = injectiveMoment H raw6114step1 := by
      have heq : raw6114step1 = (fun i j => raw6114step0 (permutation29 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6114step0 permutation29 permutation8
    _ = injectiveMoment H node246 := by rfl

def raw6115 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![1, -1, 1, -1], ![0, 2, 1, -3]]

def raw6115step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw6115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6115 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6115 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw6115 = injectiveMoment H raw6115step0 := by
      have heq : raw6115step0 = raw6115.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6115).symm
    injectiveMoment H raw6115step0 = injectiveMoment H raw6115step1 := by
      have heq : raw6115step1 = (fun i j => raw6115step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6115step0 permutation29 permutation6
    _ = injectiveMoment H node246 := by rfl

def raw6116 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![1, -1, 2, -2], ![0, 2, 0, -2]]

def raw6116step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0], ![4, -2, -2]]

def raw6116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical6116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6116 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw6116 = injectiveMoment H raw6116step0 := by
      have heq : raw6116step0 = raw6116.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6116).symm
    injectiveMoment H raw6116step0 = injectiveMoment H raw6116step1 := by
      have heq : raw6116step1 = (fun i j => raw6116step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6116step0 permutation28 permutation8
    _ = injectiveMoment H node146 := by rfl

def raw6117 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![1, -1, 3, -3], ![0, 2, -1, -1]]

def raw6117step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-2, 3, -1], ![4, -3, -1]]

def raw6117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![2, -3, 1], ![-4, 3, 1]]

def raw6117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical6117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6117 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw6117 = injectiveMoment H raw6117step0 := by
      have heq : raw6117step0 = raw6117.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6117).symm
    injectiveMoment H raw6117step0 = injectiveMoment H raw6117step1 := by
      have heq : raw6117step1 = -raw6117step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6117step0).symm
    injectiveMoment H raw6117step1 = injectiveMoment H raw6117step2 := by
      have heq : raw6117step2 = (fun i j => raw6117step1 (permutation15 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6117step1 permutation15 permutation8
    _ = injectiveMoment H node228 := by rfl

def raw6118 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw6118step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical6118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6118 = injectiveMoment H node2559 := by
  calc
    injectiveMoment H raw6118 = injectiveMoment H raw6118step0 := by
      have heq : raw6118step0 = (fun i j => raw6118 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6118 permutation42 permutation21
    _ = injectiveMoment H node2559 := by rfl

def raw6119 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical6119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6119 = injectiveMoment H node2509 := by
  rfl

def raw6120 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6120step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical6120 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6120 = injectiveMoment H node2509 := by
  calc
    injectiveMoment H raw6120 = injectiveMoment H raw6120step0 := by
      have heq : raw6120step0 = (fun i j => raw6120 (permutation35 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6120 permutation35 permutation15
    _ = injectiveMoment H node2509 := by rfl

def raw6121 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw6121step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 1, -1, -1], ![-1, 0, -1, 2], ![-1, -2, 1, 2]]

def raw6121step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical6121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6121 = injectiveMoment H node502 := by
  calc
    injectiveMoment H raw6121 = injectiveMoment H raw6121step0 := by
      have heq : raw6121step0 = -raw6121 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6121).symm
    injectiveMoment H raw6121step0 = injectiveMoment H raw6121step1 := by
      have heq : raw6121step1 = (fun i j => raw6121step0 (permutation32 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6121step0 permutation32 permutation15
    _ = injectiveMoment H node502 := by rfl

def raw6122 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 1, 1, -3], ![1, 1, -1, -1]]

def raw6122step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical6122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6122 = injectiveMoment H node924 := by
  calc
    injectiveMoment H raw6122 = injectiveMoment H raw6122step0 := by
      have heq : raw6122step0 = (fun i j => raw6122 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6122 permutation10 permutation9
    _ = injectiveMoment H node924 := by rfl

def raw6123 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw6123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 1, -2, 0], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, -1, 0, 2]]

def raw6123step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical6123 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6123 = injectiveMoment H node2315 := by
  calc
    injectiveMoment H raw6123 = injectiveMoment H raw6123step0 := by
      have heq : raw6123step0 = -raw6123 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6123).symm
    injectiveMoment H raw6123step0 = injectiveMoment H raw6123step1 := by
      have heq : raw6123step1 = (fun i j => raw6123step0 (permutation79 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6123step0 permutation79 permutation21
    _ = injectiveMoment H node2315 := by rfl

def raw6124 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6124step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 1, -2, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw6124step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical6124 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6124 = injectiveMoment H node2318 := by
  calc
    injectiveMoment H raw6124 = injectiveMoment H raw6124step0 := by
      have heq : raw6124step0 = -raw6124 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6124).symm
    injectiveMoment H raw6124step0 = injectiveMoment H raw6124step1 := by
      have heq : raw6124step1 = (fun i j => raw6124step0 (permutation71 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6124step0 permutation71 permutation21
    _ = injectiveMoment H node2318 := by rfl

def raw6125 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw6125step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![-1, 2, -1, 0], ![3, 0, -1, -2]]

def raw6125step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical6125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6125 = injectiveMoment H node477 := by
  calc
    injectiveMoment H raw6125 = injectiveMoment H raw6125step0 := by
      have heq : raw6125step0 = raw6125.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6125).symm
    injectiveMoment H raw6125step0 = injectiveMoment H raw6125step1 := by
      have heq : raw6125step1 = (fun i j => raw6125step0 (permutation31 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6125step0 permutation31 permutation32
    _ = injectiveMoment H node477 := by rfl

def raw6126 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw6126step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6126 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6126 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw6126 = injectiveMoment H raw6126step0 := by
      have heq : raw6126step0 = (fun i j => raw6126 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6126 permutation9 permutation15
    _ = injectiveMoment H node936 := by rfl

def raw6127 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6127step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw6127step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical6127 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6127 = injectiveMoment H node2063 := by
  calc
    injectiveMoment H raw6127 = injectiveMoment H raw6127step0 := by
      have heq : raw6127step0 = -raw6127 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6127).symm
    injectiveMoment H raw6127step0 = injectiveMoment H raw6127step1 := by
      have heq : raw6127step1 = (fun i j => raw6127step0 (permutation79 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6127step0 permutation79 permutation23
    _ = injectiveMoment H node2063 := by rfl

def raw6128 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6128 = injectiveMoment H node2513 := by
  rfl

def raw6129 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw6129step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6129 = injectiveMoment H node2541 := by
  calc
    injectiveMoment H raw6129 = injectiveMoment H raw6129step0 := by
      have heq : raw6129step0 = (fun i j => raw6129 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6129 permutation36 permutation15
    _ = injectiveMoment H node2541 := by rfl

def raw6130 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6130step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6130 = injectiveMoment H node2542 := by
  calc
    injectiveMoment H raw6130 = injectiveMoment H raw6130step0 := by
      have heq : raw6130step0 = (fun i j => raw6130 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6130 permutation36 permutation15
    _ = injectiveMoment H node2542 := by rfl

def raw6131 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6131step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw6131step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical6131 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6131 = injectiveMoment H node2070 := by
  calc
    injectiveMoment H raw6131 = injectiveMoment H raw6131step0 := by
      have heq : raw6131step0 = -raw6131 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6131).symm
    injectiveMoment H raw6131step0 = injectiveMoment H raw6131step1 := by
      have heq : raw6131step1 = (fun i j => raw6131step0 (permutation65 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6131step0 permutation65 permutation23
    _ = injectiveMoment H node2070 := by rfl

def raw6132 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical6132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6132 = injectiveMoment H node2514 := by
  rfl

def raw6133 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw6133step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical6133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6133 = injectiveMoment H node2532 := by
  calc
    injectiveMoment H raw6133 = injectiveMoment H raw6133step0 := by
      have heq : raw6133step0 = (fun i j => raw6133 (permutation55 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6133 permutation55 permutation17
    _ = injectiveMoment H node2532 := by rfl

def raw6134 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical6134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6134 = injectiveMoment H node2515 := by
  rfl

def raw6135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw6135step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6135 = injectiveMoment H node2540 := by
  calc
    injectiveMoment H raw6135 = injectiveMoment H raw6135step0 := by
      have heq : raw6135step0 = (fun i j => raw6135 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6135 permutation36 permutation15
    _ = injectiveMoment H node2540 := by rfl

def raw6136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw6136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical6136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6136 = injectiveMoment H node944 := by
  calc
    injectiveMoment H raw6136 = injectiveMoment H raw6136step0 := by
      have heq : raw6136step0 = (fun i j => raw6136 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6136 permutation10 permutation15
    _ = injectiveMoment H node944 := by rfl

def raw6137 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw6137step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -2, 2, 0], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw6137step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem canonical6137 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6137 = injectiveMoment H node2022 := by
  calc
    injectiveMoment H raw6137 = injectiveMoment H raw6137step0 := by
      have heq : raw6137step0 = -raw6137 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6137).symm
    injectiveMoment H raw6137step0 = injectiveMoment H raw6137step1 := by
      have heq : raw6137step1 = (fun i j => raw6137step0 (permutation101 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6137step0 permutation101 permutation16
    _ = injectiveMoment H node2022 := by rfl

def raw6138 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw6138step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -2, 2, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw6138step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical6138 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6138 = injectiveMoment H node2019 := by
  calc
    injectiveMoment H raw6138 = injectiveMoment H raw6138step0 := by
      have heq : raw6138step0 = -raw6138 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6138).symm
    injectiveMoment H raw6138step0 = injectiveMoment H raw6138step1 := by
      have heq : raw6138step1 = (fun i j => raw6138step0 (permutation101 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6138step0 permutation101 permutation16
    _ = injectiveMoment H node2019 := by rfl

def raw6139 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw6139step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -2, 1, 1], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw6139step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical6139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6139 = injectiveMoment H node2074 := by
  calc
    injectiveMoment H raw6139 = injectiveMoment H raw6139step0 := by
      have heq : raw6139step0 = -raw6139 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6139).symm
    injectiveMoment H raw6139step0 = injectiveMoment H raw6139step1 := by
      have heq : raw6139step1 = (fun i j => raw6139step0 (permutation101 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6139step0 permutation101 permutation16
    _ = injectiveMoment H node2074 := by rfl

def raw6140 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6140step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6140step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical6140 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6140 = injectiveMoment H node1993 := by
  calc
    injectiveMoment H raw6140 = injectiveMoment H raw6140step0 := by
      have heq : raw6140step0 = -raw6140 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6140).symm
    injectiveMoment H raw6140step0 = injectiveMoment H raw6140step1 := by
      have heq : raw6140step1 = (fun i j => raw6140step0 (permutation91 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6140step0 permutation91 permutation17
    _ = injectiveMoment H node1993 := by rfl

def raw6141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw6141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -2, 2, 1]]

def raw6141step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical6141 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6141 = injectiveMoment H node515 := by
  calc
    injectiveMoment H raw6141 = injectiveMoment H raw6141step0 := by
      have heq : raw6141step0 = -raw6141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6141).symm
    injectiveMoment H raw6141step0 = injectiveMoment H raw6141step1 := by
      have heq : raw6141step1 = (fun i j => raw6141step0 (permutation30 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6141step0 permutation30 permutation16
    _ = injectiveMoment H node515 := by rfl

def raw6142 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6142step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6142 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6142 = injectiveMoment H node942 := by
  calc
    injectiveMoment H raw6142 = injectiveMoment H raw6142step0 := by
      have heq : raw6142step0 = (fun i j => raw6142 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6142 permutation9 permutation15
    _ = injectiveMoment H node942 := by rfl

def raw6143 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw6143step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical6143 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6143 = injectiveMoment H node943 := by
  calc
    injectiveMoment H raw6143 = injectiveMoment H raw6143step0 := by
      have heq : raw6143step0 = (fun i j => raw6143 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6143 permutation9 permutation15
    _ = injectiveMoment H node943 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
