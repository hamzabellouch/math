import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def raw7232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical7232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7232 = injectiveMoment H node1268 := by
  calc
    injectiveMoment H raw7232 = injectiveMoment H raw7232step0 := by
      have heq : raw7232step0 = (fun i j => raw7232 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7232 permutation11 permutation9
    _ = injectiveMoment H node1268 := by rfl

def raw7233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2]]

def raw7233step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -1, -1, 3], ![2, 0, 0, -2]]

def raw7233step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical7233 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7233 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw7233 = injectiveMoment H raw7233step0 := by
      have heq : raw7233step0 = raw7233.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7233).symm
    injectiveMoment H raw7233step0 = injectiveMoment H raw7233step1 := by
      have heq : raw7233step1 = (fun i j => raw7233step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7233step0 permutation22 permutation17
    _ = injectiveMoment H node959 := by rfl

def raw7234 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw7234step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical7234 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7234 = injectiveMoment H node3376 := by
  calc
    injectiveMoment H raw7234 = injectiveMoment H raw7234step0 := by
      have heq : raw7234step0 = (fun i j => raw7234 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7234 permutation258 permutation9
    _ = injectiveMoment H node3376 := by rfl

def raw7235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7235step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -1, 0, 2], ![2, 0, -1, -1]]

def raw7235step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![1, 1, 0, -2], ![-2, 0, 1, 1]]

def raw7235step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical7235 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7235 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw7235 = injectiveMoment H raw7235step0 := by
      have heq : raw7235step0 = raw7235.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7235).symm
    injectiveMoment H raw7235step0 = injectiveMoment H raw7235step1 := by
      have heq : raw7235step1 = -raw7235step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7235step0).symm
    injectiveMoment H raw7235step1 = injectiveMoment H raw7235step2 := by
      have heq : raw7235step2 = (fun i j => raw7235step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7235step1 permutation16 permutation17
    _ = injectiveMoment H node1047 := by rfl

def raw7236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7236step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical7236 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7236 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw7236 = injectiveMoment H raw7236step0 := by
      have heq : raw7236step0 = (fun i j => raw7236 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7236 permutation9 permutation11
    _ = injectiveMoment H node1000 := by rfl

def raw7237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw7237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical7237 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7237 = injectiveMoment H node1003 := by
  calc
    injectiveMoment H raw7237 = injectiveMoment H raw7237step0 := by
      have heq : raw7237step0 = (fun i j => raw7237 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7237 permutation9 permutation11
    _ = injectiveMoment H node1003 := by rfl

def raw7238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw7238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -1, 3, -1], ![2, 0, -4, 2]]

def raw7238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical7238 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7238 = injectiveMoment H node940 := by
  calc
    injectiveMoment H raw7238 = injectiveMoment H raw7238step0 := by
      have heq : raw7238step0 = raw7238.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7238).symm
    injectiveMoment H raw7238step0 = injectiveMoment H raw7238step1 := by
      have heq : raw7238step1 = (fun i j => raw7238step0 (permutation22 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7238step0 permutation22 permutation16
    _ = injectiveMoment H node940 := by rfl

def raw7239 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw7239step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![0, -1, -3, 4]]

def raw7239step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical7239 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7239 = injectiveMoment H node3410 := by
  calc
    injectiveMoment H raw7239 = injectiveMoment H raw7239step0 := by
      have heq : raw7239step0 = -raw7239 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7239).symm
    injectiveMoment H raw7239step0 = injectiveMoment H raw7239step1 := by
      have heq : raw7239step1 = (fun i j => raw7239step0 (permutation335 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7239step0 permutation335 permutation15
    _ = injectiveMoment H node3410 := by rfl

def raw7240 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw7240step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical7240 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7240 = injectiveMoment H node3377 := by
  calc
    injectiveMoment H raw7240 = injectiveMoment H raw7240step0 := by
      have heq : raw7240step0 = (fun i j => raw7240 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7240 permutation262 permutation9
    _ = injectiveMoment H node3377 := by rfl

def raw7241 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw7241step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2]]

def raw7241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7241 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7241 = injectiveMoment H raw7241step0 := by
      have heq : raw7241step0 = raw7241.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7241).symm
    injectiveMoment H raw7241step0 = injectiveMoment H raw7241step1 := by
      have heq : raw7241step1 = (fun i j => raw7241step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7241step0 permutation22 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw7242 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1]]

def raw7242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7242 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7242 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw7242 = injectiveMoment H raw7242step0 := by
      have heq : raw7242step0 = raw7242.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7242).symm
    injectiveMoment H raw7242step0 = injectiveMoment H raw7242step1 := by
      have heq : raw7242step1 = (fun i j => raw7242step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7242step0 permutation28 permutation6
    _ = injectiveMoment H node287 := by rfl

def raw7243 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7243step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0]]

def raw7243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7243 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw7243 = injectiveMoment H raw7243step0 := by
      have heq : raw7243step0 = raw7243.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7243).symm
    injectiveMoment H raw7243step0 = injectiveMoment H raw7243step1 := by
      have heq : raw7243step1 = (fun i j => raw7243step0 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7243step0 permutation18 permutation7
    _ = injectiveMoment H node294 := by rfl

def raw7244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 2, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical7244 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7244 = injectiveMoment H node1003 := by
  calc
    injectiveMoment H raw7244 = injectiveMoment H raw7244step0 := by
      have heq : raw7244step0 = (fun i j => raw7244 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7244 permutation11 permutation11
    _ = injectiveMoment H node1003 := by rfl

def raw7245 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1]]

def raw7245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 3, -1]]

def raw7245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7245 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7245 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw7245 = injectiveMoment H raw7245step0 := by
      have heq : raw7245step0 = raw7245.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7245).symm
    injectiveMoment H raw7245step0 = injectiveMoment H raw7245step1 := by
      have heq : raw7245step1 = -raw7245step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7245step0).symm
    injectiveMoment H raw7245step1 = injectiveMoment H raw7245step2 := by
      have heq : raw7245step2 = (fun i j => raw7245step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7245step1 permutation29 permutation4
    _ = injectiveMoment H node181 := by rfl

def raw7246 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw7246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![2, -4, 2]]

def raw7246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -3, 2], ![-2, 4, -2]]

def raw7246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7246 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7246 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw7246 = injectiveMoment H raw7246step0 := by
      have heq : raw7246step0 = raw7246.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7246).symm
    injectiveMoment H raw7246step0 = injectiveMoment H raw7246step1 := by
      have heq : raw7246step1 = -raw7246step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7246step0).symm
    injectiveMoment H raw7246step1 = injectiveMoment H raw7246step2 := by
      have heq : raw7246step2 = (fun i j => raw7246step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7246step1 permutation29 permutation4
    _ = injectiveMoment H node149 := by rfl

def raw7247 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7247step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-1, 1, 0], ![2, -3, 1]]

def raw7247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![-2, 3, -1]]

def raw7247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7247 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7247 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw7247 = injectiveMoment H raw7247step0 := by
      have heq : raw7247step0 = raw7247.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7247).symm
    injectiveMoment H raw7247step0 = injectiveMoment H raw7247step1 := by
      have heq : raw7247step1 = -raw7247step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7247step0).symm
    injectiveMoment H raw7247step1 = injectiveMoment H raw7247step2 := by
      have heq : raw7247step2 = (fun i j => raw7247step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7247step1 permutation29 permutation4
    _ = injectiveMoment H node185 := by rfl

def raw7248 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw7248step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1], ![2, -4, 2]]

def raw7248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![1, -2, 1], ![-2, 4, -2]]

def raw7248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7248 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7248 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw7248 = injectiveMoment H raw7248step0 := by
      have heq : raw7248step0 = raw7248.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7248).symm
    injectiveMoment H raw7248step0 = injectiveMoment H raw7248step1 := by
      have heq : raw7248step1 = -raw7248step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7248step0).symm
    injectiveMoment H raw7248step1 = injectiveMoment H raw7248step2 := by
      have heq : raw7248step2 = (fun i j => raw7248step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7248step1 permutation29 permutation4
    _ = injectiveMoment H node153 := by rfl

def raw7249 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![1, -1, 3, -3], ![0, 1, -2, 1]]

def raw7249step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![2, -3, 1]]

def raw7249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7249 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw7249 = injectiveMoment H raw7249step0 := by
      have heq : raw7249step0 = raw7249.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7249).symm
    injectiveMoment H raw7249step0 = injectiveMoment H raw7249step1 := by
      have heq : raw7249step1 = (fun i j => raw7249step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7249step0 permutation21 permutation7
    _ = injectiveMoment H node174 := by rfl

def raw7250 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 2, 2, -1], ![4, -2, -2, 0]]

def raw7250step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7250 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7250 = injectiveMoment H node256 := by
  calc
    injectiveMoment H raw7250 = injectiveMoment H raw7250step0 := by
      have heq : raw7250step0 = raw7250.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7250).symm
    _ = injectiveMoment H node256 := by rfl

def raw7251 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 2, 2], ![3, 2, -2, -3]]

def raw7251step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 2, -2], ![1, 2, -3]]

theorem canonical7251 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7251 = injectiveMoment H node264 := by
  calc
    injectiveMoment H raw7251 = injectiveMoment H raw7251step0 := by
      have heq : raw7251step0 = raw7251.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7251).symm
    _ = injectiveMoment H node264 := by rfl

def raw7252 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 3, 1], ![3, 2, -3, -2]]

def raw7252step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

theorem canonical7252 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7252 = injectiveMoment H node265 := by
  calc
    injectiveMoment H raw7252 = injectiveMoment H raw7252step0 := by
      have heq : raw7252step0 = raw7252.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7252).symm
    _ = injectiveMoment H node265 := by rfl

def raw7253 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 4, 0], ![3, 2, -4, -1]]

def raw7253step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

theorem canonical7253 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7253 = injectiveMoment H node266 := by
  calc
    injectiveMoment H raw7253 = injectiveMoment H raw7253step0 := by
      have heq : raw7253step0 = raw7253.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7253).symm
    _ = injectiveMoment H node266 := by rfl

def raw7254 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 2, 2, -2], ![3, -2, -2, 1]]

def raw7254step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

theorem canonical7254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7254 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw7254 = injectiveMoment H raw7254step0 := by
      have heq : raw7254step0 = raw7254.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7254).symm
    _ = injectiveMoment H node274 := by rfl

def raw7255 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -3, 3, 1], ![2, 3, -3, -2]]

def raw7255step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

theorem canonical7255 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7255 = injectiveMoment H node277 := by
  calc
    injectiveMoment H raw7255 = injectiveMoment H raw7255step0 := by
      have heq : raw7255step0 = raw7255.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7255).symm
    _ = injectiveMoment H node277 := by rfl

def raw7256 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -3, 4, 0], ![2, 3, -4, -1]]

def raw7256step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

theorem canonical7256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7256 = injectiveMoment H node278 := by
  calc
    injectiveMoment H raw7256 = injectiveMoment H raw7256step0 := by
      have heq : raw7256step0 = raw7256.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7256).symm
    _ = injectiveMoment H node278 := by rfl

def raw7257 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![2, 2, -2, -2]]

def raw7257step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical7257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7257 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw7257 = injectiveMoment H raw7257step0 := by
      have heq : raw7257step0 = raw7257.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7257).symm
    _ = injectiveMoment H node279 := by rfl

def raw7258 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 3, 0], ![2, 2, -3, -1]]

def raw7258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7258 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw7258 = injectiveMoment H raw7258step0 := by
      have heq : raw7258step0 = raw7258.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7258).symm
    _ = injectiveMoment H node280 := by rfl

def raw7259 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 4, -1], ![2, 2, -4, 0]]

def raw7259step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7259 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7259 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw7259 = injectiveMoment H raw7259step0 := by
      have heq : raw7259step0 = raw7259.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7259).symm
    _ = injectiveMoment H node281 := by rfl

def raw7260 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw7260step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw7260step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical7260 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7260 = injectiveMoment H node2938 := by
  calc
    injectiveMoment H raw7260 = injectiveMoment H raw7260step0 := by
      have heq : raw7260step0 = -raw7260 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7260).symm
    injectiveMoment H raw7260step0 = injectiveMoment H raw7260step1 := by
      have heq : raw7260step1 = (fun i j => raw7260step0 (permutation356 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7260step0 permutation356 permutation21
    _ = injectiveMoment H node2938 := by rfl

def raw7261 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw7261step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw7261step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical7261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7261 = injectiveMoment H node2910 := by
  calc
    injectiveMoment H raw7261 = injectiveMoment H raw7261step0 := by
      have heq : raw7261step0 = -raw7261 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7261).symm
    injectiveMoment H raw7261step0 = injectiveMoment H raw7261step1 := by
      have heq : raw7261step1 = (fun i j => raw7261step0 (permutation408 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7261step0 permutation408 permutation9
    _ = injectiveMoment H node2910 := by rfl

def raw7262 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw7262step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw7262step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical7262 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7262 = injectiveMoment H node2971 := by
  calc
    injectiveMoment H raw7262 = injectiveMoment H raw7262step0 := by
      have heq : raw7262step0 = -raw7262 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7262).symm
    injectiveMoment H raw7262step0 = injectiveMoment H raw7262step1 := by
      have heq : raw7262step1 = (fun i j => raw7262step0 (permutation366 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7262step0 permutation366 permutation11
    _ = injectiveMoment H node2971 := by rfl

def raw7263 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw7263step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw7263step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical7263 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7263 = injectiveMoment H node3353 := by
  calc
    injectiveMoment H raw7263 = injectiveMoment H raw7263step0 := by
      have heq : raw7263step0 = -raw7263 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7263).symm
    injectiveMoment H raw7263step0 = injectiveMoment H raw7263step1 := by
      have heq : raw7263step1 = (fun i j => raw7263step0 (permutation408 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7263step0 permutation408 permutation9
    _ = injectiveMoment H node3353 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
