import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9248 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![1, -1, 2, -2]]

def raw9248step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, -1, 0, 2], ![1, 1, 0, -2]]

def raw9248step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical9248 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9248 = injectiveMoment H node1039 := by
  calc
    injectiveMoment H raw9248 = injectiveMoment H raw9248step0 := by
      have heq : raw9248step0 = raw9248.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9248).symm
    injectiveMoment H raw9248step0 = injectiveMoment H raw9248step1 := by
      have heq : raw9248step1 = (fun i j => raw9248step0 (permutation21 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9248step0 permutation21 permutation9
    _ = injectiveMoment H node1039 := by rfl

def raw9249 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -2, 3, -2]]

def raw9249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3], ![1, 1, 0, -2]]

def raw9249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical9249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9249 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw9249 = injectiveMoment H raw9249step0 := by
      have heq : raw9249step0 = raw9249.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9249).symm
    injectiveMoment H raw9249step0 = injectiveMoment H raw9249step1 := by
      have heq : raw9249step1 = (fun i j => raw9249step0 (permutation21 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9249step0 permutation21 permutation9
    _ = injectiveMoment H node959 := by rfl

def raw9250 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -2, 0, 1]]

def raw9250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, -1, 2, 0], ![1, 1, -3, 1]]

def raw9250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -2, 2], ![1, 1, -2, 0], ![-1, -1, 3, -1]]

def raw9250step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical9250 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9250 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw9250 = injectiveMoment H raw9250step0 := by
      have heq : raw9250step0 = raw9250.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9250).symm
    injectiveMoment H raw9250step0 = injectiveMoment H raw9250step1 := by
      have heq : raw9250step1 = -raw9250step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9250step0).symm
    injectiveMoment H raw9250step1 = injectiveMoment H raw9250step2 := by
      have heq : raw9250step2 = (fun i j => raw9250step1 (permutation27 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9250step1 permutation27 permutation10
    _ = injectiveMoment H node959 := by rfl

def raw9251 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 3, -4], ![1, -2, -1, 2]]

def raw9251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, -1, 3, -1], ![1, 1, -4, 2]]

def raw9251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -2, 2], ![1, 1, -3, 1], ![-1, -1, 4, -2]]

def raw9251step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 1, -3]]

theorem canonical9251 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9251 = injectiveMoment H node904 := by
  calc
    injectiveMoment H raw9251 = injectiveMoment H raw9251step0 := by
      have heq : raw9251step0 = raw9251.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9251).symm
    injectiveMoment H raw9251step0 = injectiveMoment H raw9251step1 := by
      have heq : raw9251step1 = -raw9251step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9251step0).symm
    injectiveMoment H raw9251step1 = injectiveMoment H raw9251step2 := by
      have heq : raw9251step2 = (fun i j => raw9251step1 (permutation27 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9251step1 permutation27 permutation10
    _ = injectiveMoment H node904 := by rfl

def raw9252 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw9252step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw9252step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9252 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9252 = injectiveMoment H node2931 := by
  calc
    injectiveMoment H raw9252 = injectiveMoment H raw9252step0 := by
      have heq : raw9252step0 = -raw9252 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9252).symm
    injectiveMoment H raw9252step0 = injectiveMoment H raw9252step1 := by
      have heq : raw9252step1 = (fun i j => raw9252step0 (permutation313 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9252step0 permutation313 permutation15
    _ = injectiveMoment H node2931 := by rfl

def raw9253 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw9253step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical9253 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9253 = injectiveMoment H node3300 := by
  calc
    injectiveMoment H raw9253 = injectiveMoment H raw9253step0 := by
      have heq : raw9253step0 = (fun i j => raw9253 (permutation283 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9253 permutation283 permutation9
    _ = injectiveMoment H node3300 := by rfl

def raw9254 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw9254step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 1, 0, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw9254step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9254 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9254 = injectiveMoment H node3324 := by
  calc
    injectiveMoment H raw9254 = injectiveMoment H raw9254step0 := by
      have heq : raw9254step0 = -raw9254 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9254).symm
    injectiveMoment H raw9254step0 = injectiveMoment H raw9254step1 := by
      have heq : raw9254step1 = (fun i j => raw9254step0 (permutation295 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9254step0 permutation295 permutation15
    _ = injectiveMoment H node3324 := by rfl

def raw9255 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def raw9255step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical9255 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9255 = injectiveMoment H node3464 := by
  calc
    injectiveMoment H raw9255 = injectiveMoment H raw9255step0 := by
      have heq : raw9255step0 = (fun i j => raw9255 (permutation284 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9255 permutation284 permutation9
    _ = injectiveMoment H node3464 := by rfl

def raw9256 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def raw9256step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical9256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9256 = injectiveMoment H node3401 := by
  calc
    injectiveMoment H raw9256 = injectiveMoment H raw9256step0 := by
      have heq : raw9256step0 = (fun i j => raw9256 (permutation284 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9256 permutation284 permutation9
    _ = injectiveMoment H node3401 := by rfl

def raw9257 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw9257step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw9257step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem canonical9257 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9257 = injectiveMoment H node2943 := by
  calc
    injectiveMoment H raw9257 = injectiveMoment H raw9257step0 := by
      have heq : raw9257step0 = -raw9257 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9257).symm
    injectiveMoment H raw9257step0 = injectiveMoment H raw9257step1 := by
      have heq : raw9257step1 = (fun i j => raw9257step0 (permutation373 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9257step0 permutation373 permutation9
    _ = injectiveMoment H node2943 := by rfl

def raw9258 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def raw9258step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw9258step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9258 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9258 = injectiveMoment H node3039 := by
  calc
    injectiveMoment H raw9258 = injectiveMoment H raw9258step0 := by
      have heq : raw9258step0 = -raw9258 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9258).symm
    injectiveMoment H raw9258step0 = injectiveMoment H raw9258step1 := by
      have heq : raw9258step1 = (fun i j => raw9258step0 (permutation363 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9258step0 permutation363 permutation11
    _ = injectiveMoment H node3039 := by rfl

def raw9259 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def raw9259step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9259 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9259 = injectiveMoment H node3081 := by
  calc
    injectiveMoment H raw9259 = injectiveMoment H raw9259step0 := by
      have heq : raw9259step0 = (fun i j => raw9259 (permutation356 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9259 permutation356 permutation14
    _ = injectiveMoment H node3081 := by rfl

def raw9260 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, -2, 3, -2]]

def raw9260step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![-1, 2, -3, 2]]

def raw9260step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1]]

theorem canonical9260 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9260 = injectiveMoment H node2860 := by
  calc
    injectiveMoment H raw9260 = injectiveMoment H raw9260step0 := by
      have heq : raw9260step0 = -raw9260 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9260).symm
    injectiveMoment H raw9260step0 = injectiveMoment H raw9260step1 := by
      have heq : raw9260step1 = (fun i j => raw9260step0 (permutation128 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9260step0 permutation128 permutation9
    _ = injectiveMoment H node2860 := by rfl

def raw9261 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -2, 1, 0]]

def raw9261step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1]]

theorem canonical9261 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9261 = injectiveMoment H node2860 := by
  calc
    injectiveMoment H raw9261 = injectiveMoment H raw9261step0 := by
      have heq : raw9261step0 = (fun i j => raw9261 (permutation104 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9261 permutation104 permutation10
    _ = injectiveMoment H node2860 := by rfl

def raw9262 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 3, -4], ![1, -2, 0, 1]]

def raw9262step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -3, 4], ![-1, 2, 0, -1]]

def raw9262step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -3, 4]]

theorem canonical9262 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9262 = injectiveMoment H node2862 := by
  calc
    injectiveMoment H raw9262 = injectiveMoment H raw9262step0 := by
      have heq : raw9262step0 = -raw9262 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9262).symm
    injectiveMoment H raw9262step0 = injectiveMoment H raw9262step1 := by
      have heq : raw9262step1 = (fun i j => raw9262step0 (permutation128 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9262step0 permutation128 permutation9
    _ = injectiveMoment H node2862 := by rfl

def raw9263 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def raw9263step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0], ![-1, -2, -1, 4]]

def raw9263step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical9263 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9263 = injectiveMoment H node3331 := by
  calc
    injectiveMoment H raw9263 = injectiveMoment H raw9263step0 := by
      have heq : raw9263step0 = -raw9263 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9263).symm
    injectiveMoment H raw9263step0 = injectiveMoment H raw9263step1 := by
      have heq : raw9263step1 = (fun i j => raw9263step0 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9263step0 permutation308 permutation9
    _ = injectiveMoment H node3331 := by rfl

def raw9264 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, -1, 3, -2]]

def raw9264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw9264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical9264 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9264 = injectiveMoment H node884 := by
  calc
    injectiveMoment H raw9264 = injectiveMoment H raw9264step0 := by
      have hz : ∀ i, raw9264 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9264step0 = (fun i j => raw9264 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9264 permutation9 hz
    injectiveMoment H raw9264step0 = injectiveMoment H raw9264step1 := by
      have heq : raw9264step1 = (fun i j => raw9264step0 (permutation128 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9264step0 permutation128 permutation4
    _ = injectiveMoment H node884 := by rfl

def raw9265 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![0, -1, 1, 0]]

def raw9265step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![0, 1, -1, 0]]

def raw9265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![1, -1, 0]]

def raw9265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical9265 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9265 = injectiveMoment H node884 := by
  calc
    injectiveMoment H raw9265 = injectiveMoment H raw9265step0 := by
      have heq : raw9265step0 = -raw9265 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9265).symm
    injectiveMoment H raw9265step0 = injectiveMoment H raw9265step1 := by
      have hz : ∀ i, raw9265step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9265step1 = (fun i j => raw9265step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9265step0 permutation9 hz
    injectiveMoment H raw9265step1 = injectiveMoment H raw9265step2 := by
      have heq : raw9265step2 = (fun i j => raw9265step1 (permutation104 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9265step1 permutation104 permutation3
    _ = injectiveMoment H node884 := by rfl

def raw9266 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![0, -1, 0, 1]]

def raw9266step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -3, 4], ![0, 1, 0, -1]]

def raw9266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -3, 4], ![1, 0, -1]]

def raw9266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical9266 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9266 = injectiveMoment H node748 := by
  calc
    injectiveMoment H raw9266 = injectiveMoment H raw9266step0 := by
      have heq : raw9266step0 = -raw9266 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9266).symm
    injectiveMoment H raw9266step0 = injectiveMoment H raw9266step1 := by
      have hz : ∀ i, raw9266step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9266step1 = (fun i j => raw9266step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9266step0 permutation9 hz
    injectiveMoment H raw9266step1 = injectiveMoment H raw9266step2 := by
      have heq : raw9266step2 = (fun i j => raw9266step1 (permutation104 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9266step1 permutation104 permutation3
    _ = injectiveMoment H node748 := by rfl

def raw9267 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -2, 1, 1]]

def raw9267step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 2, -1, -1]]

def raw9267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -2, 4], ![2, -1, -1]]

def raw9267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical9267 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9267 = injectiveMoment H node437 := by
  calc
    injectiveMoment H raw9267 = injectiveMoment H raw9267step0 := by
      have heq : raw9267step0 = -raw9267 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9267).symm
    injectiveMoment H raw9267step0 = injectiveMoment H raw9267step1 := by
      have hz : ∀ i, raw9267step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9267step1 = (fun i j => raw9267step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9267step0 permutation9 hz
    injectiveMoment H raw9267step1 = injectiveMoment H raw9267step2 := by
      have heq : raw9267step2 = (fun i j => raw9267step1 (permutation104 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9267step1 permutation104 permutation3
    _ = injectiveMoment H node437 := by rfl

def raw9268 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw9268step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw9268step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem canonical9268 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9268 = injectiveMoment H node2923 := by
  calc
    injectiveMoment H raw9268 = injectiveMoment H raw9268step0 := by
      have heq : raw9268step0 = -raw9268 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9268).symm
    injectiveMoment H raw9268step0 = injectiveMoment H raw9268step1 := by
      have heq : raw9268step1 = (fun i j => raw9268step0 (permutation309 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9268step0 permutation309 permutation15
    _ = injectiveMoment H node2923 := by rfl

def raw9269 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw9269step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical9269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9269 = injectiveMoment H node3287 := by
  calc
    injectiveMoment H raw9269 = injectiveMoment H raw9269step0 := by
      have heq : raw9269step0 = (fun i j => raw9269 (permutation241 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9269 permutation241 permutation15
    _ = injectiveMoment H node3287 := by rfl

def raw9270 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw9270step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical9270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9270 = injectiveMoment H node3286 := by
  calc
    injectiveMoment H raw9270 = injectiveMoment H raw9270step0 := by
      have heq : raw9270step0 = (fun i j => raw9270 (permutation242 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9270 permutation242 permutation15
    _ = injectiveMoment H node3286 := by rfl

def raw9271 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, -1, 2, 1], ![1, 2, 1, -4]]

def raw9271step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 1, -2, -1], ![-1, -2, -1, 4]]

def raw9271step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

theorem canonical9271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9271 = injectiveMoment H node2924 := by
  calc
    injectiveMoment H raw9271 = injectiveMoment H raw9271step0 := by
      have heq : raw9271step0 = -raw9271 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9271).symm
    injectiveMoment H raw9271step0 = injectiveMoment H raw9271step1 := by
      have heq : raw9271step1 = (fun i j => raw9271step0 (permutation308 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9271step0 permutation308 permutation15
    _ = injectiveMoment H node2924 := by rfl

def raw9272 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw9272step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![-1, -1, -2, 4]]

def raw9272step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical9272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9272 = injectiveMoment H node3351 := by
  calc
    injectiveMoment H raw9272 = injectiveMoment H raw9272step0 := by
      have heq : raw9272step0 = -raw9272 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9272).symm
    injectiveMoment H raw9272step0 = injectiveMoment H raw9272step1 := by
      have heq : raw9272step1 = (fun i j => raw9272step0 (permutation309 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9272step0 permutation309 permutation15
    _ = injectiveMoment H node3351 := by rfl

def raw9273 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 1, 1, -3]]

def raw9273step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![-1, -1, -1, 3]]

def raw9273step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical9273 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9273 = injectiveMoment H node3375 := by
  calc
    injectiveMoment H raw9273 = injectiveMoment H raw9273step0 := by
      have heq : raw9273step0 = -raw9273 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9273).symm
    injectiveMoment H raw9273step0 = injectiveMoment H raw9273step1 := by
      have heq : raw9273step1 = (fun i j => raw9273step0 (permutation309 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9273step0 permutation309 permutation15
    _ = injectiveMoment H node3375 := by rfl

def raw9274 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw9274step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical9274 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9274 = injectiveMoment H node3468 := by
  calc
    injectiveMoment H raw9274 = injectiveMoment H raw9274step0 := by
      have heq : raw9274step0 = (fun i j => raw9274 (permutation242 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9274 permutation242 permutation15
    _ = injectiveMoment H node3468 := by rfl

def raw9275 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 0, 2, -3]]

def raw9275step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical9275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9275 = injectiveMoment H node3467 := by
  calc
    injectiveMoment H raw9275 = injectiveMoment H raw9275step0 := by
      have heq : raw9275step0 = (fun i j => raw9275 (permutation242 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9275 permutation242 permutation15
    _ = injectiveMoment H node3467 := by rfl

def raw9276 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 3, -3]]

def raw9276step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical9276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9276 = injectiveMoment H node3328 := by
  calc
    injectiveMoment H raw9276 = injectiveMoment H raw9276step0 := by
      have heq : raw9276step0 = (fun i j => raw9276 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9276 permutation258 permutation9
    _ = injectiveMoment H node3328 := by rfl

def raw9277 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![0, 2, 1, -3]]

def raw9277step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem canonical9277 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9277 = injectiveMoment H node3396 := by
  calc
    injectiveMoment H raw9277 = injectiveMoment H raw9277step0 := by
      have heq : raw9277step0 = (fun i j => raw9277 (permutation259 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9277 permutation259 permutation10
    _ = injectiveMoment H node3396 := by rfl

def raw9278 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def raw9278step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical9278 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9278 = injectiveMoment H node3466 := by
  calc
    injectiveMoment H raw9278 = injectiveMoment H raw9278step0 := by
      have heq : raw9278step0 = (fun i j => raw9278 (permutation241 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9278 permutation241 permutation15
    _ = injectiveMoment H node3466 := by rfl

def raw9279 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9279step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9279step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical9279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9279 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw9279 = injectiveMoment H raw9279step0 := by
      have hz : ∀ j, raw9279 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9279step0 = (fun i j => raw9279 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9279 permutation221 hz
    injectiveMoment H raw9279step0 = injectiveMoment H raw9279step1 := by
      have heq : raw9279step1 = (fun i j => raw9279step0 (permutation139 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9279step0 permutation139 permutation20
    _ = injectiveMoment H node1746 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
