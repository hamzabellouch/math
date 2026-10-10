import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9216 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9216step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9216step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9216 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9216 = injectiveMoment H node3113 := by
  calc
    injectiveMoment H raw9216 = injectiveMoment H raw9216step0 := by
      have heq : raw9216step0 = -raw9216 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9216).symm
    injectiveMoment H raw9216step0 = injectiveMoment H raw9216step1 := by
      have heq : raw9216step1 = (fun i j => raw9216step0 (permutation376 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9216step0 permutation376 permutation15
    _ = injectiveMoment H node3113 := by rfl

def raw9217 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9217step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9217 = injectiveMoment H node3273 := by
  calc
    injectiveMoment H raw9217 = injectiveMoment H raw9217step0 := by
      have heq : raw9217step0 = (fun i j => raw9217 (permutation279 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9217 permutation279 permutation9
    _ = injectiveMoment H node3273 := by rfl

def raw9218 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw9218step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem canonical9218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9218 = injectiveMoment H node2959 := by
  calc
    injectiveMoment H raw9218 = injectiveMoment H raw9218step0 := by
      have heq : raw9218step0 = (fun i j => raw9218 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9218 permutation277 permutation9
    _ = injectiveMoment H node2959 := by rfl

def raw9219 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def raw9219step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9219 = injectiveMoment H node3436 := by
  calc
    injectiveMoment H raw9219 = injectiveMoment H raw9219step0 := by
      have heq : raw9219step0 = (fun i j => raw9219 (permutation237 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9219 permutation237 permutation27
    _ = injectiveMoment H node3436 := by rfl

def raw9220 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw9220step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical9220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9220 = injectiveMoment H node3442 := by
  calc
    injectiveMoment H raw9220 = injectiveMoment H raw9220step0 := by
      have heq : raw9220step0 = (fun i j => raw9220 (permutation291 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9220 permutation291 permutation30
    _ = injectiveMoment H node3442 := by rfl

def raw9221 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw9221step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical9221 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9221 = injectiveMoment H node3434 := by
  calc
    injectiveMoment H raw9221 = injectiveMoment H raw9221step0 := by
      have heq : raw9221step0 = (fun i j => raw9221 (permutation238 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9221 permutation238 permutation28
    _ = injectiveMoment H node3434 := by rfl

def raw9222 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9222step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9222step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9222 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9222 = injectiveMoment H node3018 := by
  calc
    injectiveMoment H raw9222 = injectiveMoment H raw9222step0 := by
      have heq : raw9222step0 = -raw9222 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9222).symm
    injectiveMoment H raw9222step0 = injectiveMoment H raw9222step1 := by
      have heq : raw9222step1 = (fun i j => raw9222step0 (permutation406 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9222step0 permutation406 permutation17
    _ = injectiveMoment H node3018 := by rfl

def raw9223 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw9223step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw9223step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical9223 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9223 = injectiveMoment H node3310 := by
  calc
    injectiveMoment H raw9223 = injectiveMoment H raw9223step0 := by
      have heq : raw9223step0 = -raw9223 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9223).symm
    injectiveMoment H raw9223step0 = injectiveMoment H raw9223step1 := by
      have heq : raw9223step1 = (fun i j => raw9223step0 (permutation363 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9223step0 permutation363 permutation16
    _ = injectiveMoment H node3310 := by rfl

def raw9224 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9224step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

theorem canonical9224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9224 = injectiveMoment H node3318 := by
  calc
    injectiveMoment H raw9224 = injectiveMoment H raw9224step0 := by
      have heq : raw9224step0 = (fun i j => raw9224 (permutation363 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9224 permutation363 permutation16
    _ = injectiveMoment H node3318 := by rfl

def raw9225 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def raw9225step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical9225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9225 = injectiveMoment H node3284 := by
  calc
    injectiveMoment H raw9225 = injectiveMoment H raw9225step0 := by
      have heq : raw9225step0 = (fun i j => raw9225 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9225 permutation277 permutation9
    _ = injectiveMoment H node3284 := by rfl

def raw9226 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9226step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem canonical9226 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9226 = injectiveMoment H node3258 := by
  calc
    injectiveMoment H raw9226 = injectiveMoment H raw9226step0 := by
      have heq : raw9226step0 = (fun i j => raw9226 (permutation355 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9226 permutation355 permutation10
    _ = injectiveMoment H node3258 := by rfl

def raw9227 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9227step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical9227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9227 = injectiveMoment H node3327 := by
  calc
    injectiveMoment H raw9227 = injectiveMoment H raw9227step0 := by
      have heq : raw9227step0 = (fun i j => raw9227 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9227 permutation277 permutation9
    _ = injectiveMoment H node3327 := by rfl

def raw9228 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9228step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9228 = injectiveMoment H node3313 := by
  calc
    injectiveMoment H raw9228 = injectiveMoment H raw9228step0 := by
      have heq : raw9228step0 = (fun i j => raw9228 (permutation355 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9228 permutation355 permutation10
    _ = injectiveMoment H node3313 := by rfl

def raw9229 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9229step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9229 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9229 = injectiveMoment H node3322 := by
  calc
    injectiveMoment H raw9229 = injectiveMoment H raw9229step0 := by
      have heq : raw9229step0 = (fun i j => raw9229 (permutation356 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9229 permutation356 permutation10
    _ = injectiveMoment H node3322 := by rfl

def raw9230 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3]]

def raw9230step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 3, -3]]

def raw9230step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw9230step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical9230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9230 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw9230 = injectiveMoment H raw9230step0 := by
      have hz : ∀ i, raw9230 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw9230step0 = (fun i j => raw9230 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9230 permutation15 hz
    injectiveMoment H raw9230step0 = injectiveMoment H raw9230step1 := by
      have hz : ∀ i, raw9230step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw9230step1 = (fun i j => raw9230step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9230step0 permutation3 hz
    injectiveMoment H raw9230step1 = injectiveMoment H raw9230step2 := by
      have heq : raw9230step2 = (fun i j => raw9230step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9230step1 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw9231 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def raw9231step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem canonical9231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9231 = injectiveMoment H node3137 := by
  calc
    injectiveMoment H raw9231 = injectiveMoment H raw9231step0 := by
      have heq : raw9231step0 = (fun i j => raw9231 (permutation308 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9231 permutation308 permutation10
    _ = injectiveMoment H node3137 := by rfl

def raw9232 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def raw9232step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem canonical9232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9232 = injectiveMoment H node3296 := by
  calc
    injectiveMoment H raw9232 = injectiveMoment H raw9232step0 := by
      have heq : raw9232step0 = (fun i j => raw9232 (permutation259 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9232 permutation259 permutation10
    _ = injectiveMoment H node3296 := by rfl

def raw9233 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def raw9233step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9233 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9233 = injectiveMoment H node3244 := by
  calc
    injectiveMoment H raw9233 = injectiveMoment H raw9233step0 := by
      have heq : raw9233step0 = (fun i j => raw9233 (permutation308 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9233 permutation308 permutation10
    _ = injectiveMoment H node3244 := by rfl

def raw9234 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def raw9234step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem canonical9234 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9234 = injectiveMoment H node3268 := by
  calc
    injectiveMoment H raw9234 = injectiveMoment H raw9234step0 := by
      have heq : raw9234step0 = (fun i j => raw9234 (permutation311 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9234 permutation311 permutation16
    _ = injectiveMoment H node3268 := by rfl

def raw9235 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9235step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9235step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9235 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9235 = injectiveMoment H node3121 := by
  calc
    injectiveMoment H raw9235 = injectiveMoment H raw9235step0 := by
      have heq : raw9235step0 = -raw9235 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9235).symm
    injectiveMoment H raw9235step0 = injectiveMoment H raw9235step1 := by
      have heq : raw9235step1 = (fun i j => raw9235step0 (permutation312 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9235step0 permutation312 permutation15
    _ = injectiveMoment H node3121 := by rfl

def raw9236 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def raw9236step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![0, -2, -1, 3]]

def raw9236step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9236 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9236 = injectiveMoment H node3138 := by
  calc
    injectiveMoment H raw9236 = injectiveMoment H raw9236step0 := by
      have heq : raw9236step0 = -raw9236 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9236).symm
    injectiveMoment H raw9236step0 = injectiveMoment H raw9236step1 := by
      have heq : raw9236step1 = (fun i j => raw9236step0 (permutation312 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9236step0 permutation312 permutation15
    _ = injectiveMoment H node3138 := by rfl

def raw9237 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9237step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9237 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9237 = injectiveMoment H node3285 := by
  calc
    injectiveMoment H raw9237 = injectiveMoment H raw9237step0 := by
      have heq : raw9237step0 = (fun i j => raw9237 (permutation279 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9237 permutation279 permutation9
    _ = injectiveMoment H node3285 := by rfl

def raw9238 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def raw9238step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, -2, 1], ![1, -2, -1, 2]]

def raw9238step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9238 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9238 = injectiveMoment H node3267 := by
  calc
    injectiveMoment H raw9238 = injectiveMoment H raw9238step0 := by
      have heq : raw9238step0 = -raw9238 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9238).symm
    injectiveMoment H raw9238step0 = injectiveMoment H raw9238step1 := by
      have heq : raw9238step1 = (fun i j => raw9238step0 (permutation312 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9238step0 permutation312 permutation15
    _ = injectiveMoment H node3267 := by rfl

def raw9239 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def raw9239step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9239 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9239 = injectiveMoment H node3463 := by
  calc
    injectiveMoment H raw9239 = injectiveMoment H raw9239step0 := by
      have heq : raw9239step0 = (fun i j => raw9239 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9239 permutation395 permutation10
    _ = injectiveMoment H node3463 := by rfl

def raw9240 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def raw9240step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9240 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9240 = injectiveMoment H node3316 := by
  calc
    injectiveMoment H raw9240 = injectiveMoment H raw9240step0 := by
      have heq : raw9240step0 = (fun i j => raw9240 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9240 permutation395 permutation10
    _ = injectiveMoment H node3316 := by rfl

def raw9241 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def raw9241step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![1, -2, -2, 3]]

def raw9241step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9241 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9241 = injectiveMoment H node3225 := by
  calc
    injectiveMoment H raw9241 = injectiveMoment H raw9241step0 := by
      have heq : raw9241step0 = -raw9241 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9241).symm
    injectiveMoment H raw9241step0 = injectiveMoment H raw9241step1 := by
      have heq : raw9241step1 = (fun i j => raw9241step0 (permutation373 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9241step0 permutation373 permutation15
    _ = injectiveMoment H node3225 := by rfl

def raw9242 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def raw9242step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![1, 1, -2, 0], ![-1, -2, -1, 4]]

def raw9242step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9242 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9242 = injectiveMoment H node2930 := by
  calc
    injectiveMoment H raw9242 = injectiveMoment H raw9242step0 := by
      have heq : raw9242step0 = -raw9242 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9242).symm
    injectiveMoment H raw9242step0 = injectiveMoment H raw9242step1 := by
      have heq : raw9242step1 = (fun i j => raw9242step0 (permutation308 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9242step0 permutation308 permutation15
    _ = injectiveMoment H node2930 := by rfl

def raw9243 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw9243step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical9243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9243 = injectiveMoment H node2749 := by
  calc
    injectiveMoment H raw9243 = injectiveMoment H raw9243step0 := by
      have heq : raw9243step0 = (fun i j => raw9243 (permutation80 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9243 permutation80 permutation11
    _ = injectiveMoment H node2749 := by rfl

def raw9244 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw9244step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical9244 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9244 = injectiveMoment H node2843 := by
  calc
    injectiveMoment H raw9244 = injectiveMoment H raw9244step0 := by
      have heq : raw9244step0 = (fun i j => raw9244 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9244 permutation80 permutation9
    _ = injectiveMoment H node2843 := by rfl

def raw9245 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9245step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical9245 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9245 = injectiveMoment H node2844 := by
  calc
    injectiveMoment H raw9245 = injectiveMoment H raw9245step0 := by
      have heq : raw9245step0 = (fun i j => raw9245 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9245 permutation80 permutation9
    _ = injectiveMoment H node2844 := by rfl

def raw9246 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9246step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical9246 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9246 = injectiveMoment H node2845 := by
  calc
    injectiveMoment H raw9246 = injectiveMoment H raw9246step0 := by
      have heq : raw9246step0 = (fun i j => raw9246 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9246 permutation80 permutation9
    _ = injectiveMoment H node2845 := by rfl

def raw9247 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def raw9247step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![1, 1, -1, -1], ![-1, -1, -2, 4]]

def raw9247step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical9247 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9247 = injectiveMoment H node3345 := by
  calc
    injectiveMoment H raw9247 = injectiveMoment H raw9247step0 := by
      have heq : raw9247step0 = -raw9247 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9247).symm
    injectiveMoment H raw9247step0 = injectiveMoment H raw9247step1 := by
      have heq : raw9247step1 = (fun i j => raw9247step0 (permutation373 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9247step0 permutation373 permutation9
    _ = injectiveMoment H node3345 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
