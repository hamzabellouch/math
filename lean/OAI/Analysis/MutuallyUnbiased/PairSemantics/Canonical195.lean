import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![0, 1, -1, 0]]

def raw6240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6240 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6240 = injectiveMoment H node2548 := by
  calc
    injectiveMoment H raw6240 = injectiveMoment H raw6240step0 := by
      have heq : raw6240step0 = (fun i j => raw6240 (permutation37 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6240 permutation37 permutation9
    _ = injectiveMoment H node2548 := by rfl

def raw6241 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical6241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6241 = injectiveMoment H node963 := by
  rfl

def raw6242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw6242step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical6242 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6242 = injectiveMoment H node962 := by
  calc
    injectiveMoment H raw6242 = injectiveMoment H raw6242step0 := by
      have heq : raw6242step0 = (fun i j => raw6242 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6242 permutation10 permutation15
    _ = injectiveMoment H node962 := by rfl

def raw6243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw6243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical6243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6243 = injectiveMoment H node933 := by
  calc
    injectiveMoment H raw6243 = injectiveMoment H raw6243step0 := by
      have heq : raw6243step0 = (fun i j => raw6243 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6243 permutation9 permutation11
    _ = injectiveMoment H node933 := by rfl

def raw6244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-1, -1, 2, 0], ![3, 1, -4, 0]]

def raw6244step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![1, 1, -2, 0], ![-3, -1, 4, 0]]

def raw6244step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical6244 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6244 = injectiveMoment H node1168 := by
  calc
    injectiveMoment H raw6244 = injectiveMoment H raw6244step0 := by
      have heq : raw6244step0 = raw6244.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6244).symm
    injectiveMoment H raw6244step0 = injectiveMoment H raw6244step1 := by
      have heq : raw6244step1 = -raw6244step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6244step0).symm
    injectiveMoment H raw6244step1 = injectiveMoment H raw6244step2 := by
      have heq : raw6244step2 = (fun i j => raw6244step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6244step1 permutation27 permutation19
    _ = injectiveMoment H node1168 := by rfl

def raw6245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6245step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![3, 0, -2, -1]]

def raw6245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1]]

def raw6245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6245 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6245 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6245 = injectiveMoment H raw6245step0 := by
      have heq : raw6245step0 = raw6245.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6245).symm
    injectiveMoment H raw6245step0 = injectiveMoment H raw6245step1 := by
      have hz : ∀ i, raw6245step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw6245step1 = (fun i j => raw6245step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6245step0 permutation15 hz
    injectiveMoment H raw6245step1 = injectiveMoment H raw6245step2 := by
      have heq : raw6245step2 = (fun i j => raw6245step1 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6245step1 permutation30 permutation8
    _ = injectiveMoment H node271 := by rfl

def raw6246 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6246step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 2, -1], ![3, 0, -3, 0]]

def raw6246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![3, -3, 0]]

def raw6246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical6246 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6246 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6246 = injectiveMoment H raw6246step0 := by
      have heq : raw6246step0 = raw6246.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6246).symm
    injectiveMoment H raw6246step0 = injectiveMoment H raw6246step1 := by
      have hz : ∀ i, raw6246step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw6246step1 = (fun i j => raw6246step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6246step0 permutation15 hz
    injectiveMoment H raw6246step1 = injectiveMoment H raw6246step2 := by
      have heq : raw6246step2 = (fun i j => raw6246step1 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6246step1 permutation24 permutation7
    _ = injectiveMoment H node285 := by rfl

def raw6247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6247step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical6247 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6247 = injectiveMoment H node2534 := by
  calc
    injectiveMoment H raw6247 = injectiveMoment H raw6247step0 := by
      have heq : raw6247step0 = (fun i j => raw6247 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6247 permutation42 permutation21
    _ = injectiveMoment H node2534 := by rfl

def raw6248 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6248step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6248 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6248 = injectiveMoment H node2512 := by
  calc
    injectiveMoment H raw6248 = injectiveMoment H raw6248step0 := by
      have heq : raw6248step0 = (fun i j => raw6248 (permutation46 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6248 permutation46 permutation17
    _ = injectiveMoment H node2512 := by rfl

def raw6249 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![-1, 2, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6249step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![0, 0, -1, 1], ![1, -2, 1, 0], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw6249step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

theorem canonical6249 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6249 = injectiveMoment H node2255 := by
  calc
    injectiveMoment H raw6249 = injectiveMoment H raw6249step0 := by
      have heq : raw6249step0 = -raw6249 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6249).symm
    injectiveMoment H raw6249step0 = injectiveMoment H raw6249step1 := by
      have heq : raw6249step1 = (fun i j => raw6249step0 (permutation101 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6249step0 permutation101 permutation16
    _ = injectiveMoment H node2255 := by rfl

def raw6250 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw6250step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw6250step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

theorem canonical6250 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6250 = injectiveMoment H node2259 := by
  calc
    injectiveMoment H raw6250 = injectiveMoment H raw6250step0 := by
      have heq : raw6250step0 = -raw6250 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6250).symm
    injectiveMoment H raw6250step0 = injectiveMoment H raw6250step1 := by
      have heq : raw6250step1 = (fun i j => raw6250step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6250step0 permutation101 permutation15
    _ = injectiveMoment H node2259 := by rfl

def raw6251 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6251step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical6251 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6251 = injectiveMoment H node2537 := by
  calc
    injectiveMoment H raw6251 = injectiveMoment H raw6251step0 := by
      have heq : raw6251step0 = (fun i j => raw6251 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6251 permutation39 permutation9
    _ = injectiveMoment H node2537 := by rfl

def raw6252 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6252step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical6252 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6252 = injectiveMoment H node2538 := by
  calc
    injectiveMoment H raw6252 = injectiveMoment H raw6252step0 := by
      have heq : raw6252step0 = (fun i j => raw6252 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6252 permutation39 permutation9
    _ = injectiveMoment H node2538 := by rfl

def raw6253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6253step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical6253 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6253 = injectiveMoment H node2539 := by
  calc
    injectiveMoment H raw6253 = injectiveMoment H raw6253step0 := by
      have heq : raw6253step0 = (fun i j => raw6253 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6253 permutation39 permutation9
    _ = injectiveMoment H node2539 := by rfl

def raw6254 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6254step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6254 = injectiveMoment H node970 := by
  calc
    injectiveMoment H raw6254 = injectiveMoment H raw6254step0 := by
      have hz : ∀ j, raw6254 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw6254step0 = (fun i j => raw6254 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6254 permutation80 hz
    _ = injectiveMoment H node970 := by rfl

def raw6255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 1, 0, -2]]

def raw6255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-1, 1, 0, 0], ![3, -1, 0, -2]]

def raw6255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2]]

def raw6255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6255 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6255 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6255 = injectiveMoment H raw6255step0 := by
      have heq : raw6255step0 = raw6255.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6255).symm
    injectiveMoment H raw6255step0 = injectiveMoment H raw6255step1 := by
      have hz : ∀ i, raw6255step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw6255step1 = (fun i j => raw6255step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6255step0 permutation21 hz
    injectiveMoment H raw6255step1 = injectiveMoment H raw6255step2 := by
      have heq : raw6255step2 = (fun i j => raw6255step1 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6255step1 permutation27 permutation6
    _ = injectiveMoment H node271 := by rfl

def raw6256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

theorem canonical6256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6256 = injectiveMoment H node2550 := by
  rfl

def raw6257 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6257 = injectiveMoment H node2551 := by
  rfl

def raw6258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6258step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6258 = injectiveMoment H node2551 := by
  calc
    injectiveMoment H raw6258 = injectiveMoment H raw6258step0 := by
      have heq : raw6258step0 = (fun i j => raw6258 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6258 permutation34 permutation15
    _ = injectiveMoment H node2551 := by rfl

def raw6259 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

theorem canonical6259 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6259 = injectiveMoment H node2552 := by
  rfl

def raw6260 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6260step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6260 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6260 = injectiveMoment H node2542 := by
  calc
    injectiveMoment H raw6260 = injectiveMoment H raw6260step0 := by
      have heq : raw6260step0 = (fun i j => raw6260 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6260 permutation45 permutation11
    _ = injectiveMoment H node2542 := by rfl

def raw6261 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem canonical6261 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6261 = injectiveMoment H node966 := by
  rfl

def raw6262 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical6262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6262 = injectiveMoment H node2556 := by
  rfl

def raw6263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

theorem canonical6263 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6263 = injectiveMoment H node967 := by
  rfl

def raw6264 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![1, 1, 0, -2]]

def raw6264step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical6264 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6264 = injectiveMoment H node2530 := by
  calc
    injectiveMoment H raw6264 = injectiveMoment H raw6264step0 := by
      have heq : raw6264step0 = (fun i j => raw6264 (permutation45 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6264 permutation45 permutation9
    _ = injectiveMoment H node2530 := by rfl

def raw6265 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw6265step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6265 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6265 = injectiveMoment H node2551 := by
  calc
    injectiveMoment H raw6265 = injectiveMoment H raw6265step0 := by
      have heq : raw6265step0 = (fun i j => raw6265 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6265 permutation35 permutation9
    _ = injectiveMoment H node2551 := by rfl

def raw6266 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw6266step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical6266 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6266 = injectiveMoment H node2555 := by
  calc
    injectiveMoment H raw6266 = injectiveMoment H raw6266step0 := by
      have heq : raw6266step0 = (fun i j => raw6266 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6266 permutation35 permutation9
    _ = injectiveMoment H node2555 := by rfl

def raw6267 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6267step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6267 = injectiveMoment H node2531 := by
  calc
    injectiveMoment H raw6267 = injectiveMoment H raw6267step0 := by
      have heq : raw6267step0 = (fun i j => raw6267 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6267 permutation41 permutation11
    _ = injectiveMoment H node2531 := by rfl

def raw6268 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 1, 1, -2]]

def raw6268step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6268 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6268 = injectiveMoment H node2536 := by
  calc
    injectiveMoment H raw6268 = injectiveMoment H raw6268step0 := by
      have heq : raw6268step0 = (fun i j => raw6268 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6268 permutation40 permutation11
    _ = injectiveMoment H node2536 := by rfl

def raw6269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![0, 1, -1, 0]]

def raw6269step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2]]

theorem canonical6269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6269 = injectiveMoment H node2558 := by
  calc
    injectiveMoment H raw6269 = injectiveMoment H raw6269step0 := by
      have heq : raw6269step0 = (fun i j => raw6269 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6269 permutation34 permutation9
    _ = injectiveMoment H node2558 := by rfl

def raw6270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6270 = injectiveMoment H node969 := by
  rfl

def raw6271 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![1, 1, -1, -1]]

def raw6271step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6271 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6271 = injectiveMoment H node2531 := by
  calc
    injectiveMoment H raw6271 = injectiveMoment H raw6271step0 := by
      have heq : raw6271step0 = (fun i j => raw6271 (permutation45 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6271 permutation45 permutation9
    _ = injectiveMoment H node2531 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
