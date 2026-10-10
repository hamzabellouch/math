import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, 0, 2, -1], ![3, -1, -1, -1]]

def raw3232step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3232 = injectiveMoment H node943 := by
  calc
    injectiveMoment H raw3232 = injectiveMoment H raw3232step0 := by
      have heq : raw3232step0 = raw3232.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3232).symm
    injectiveMoment H raw3232step0 = injectiveMoment H raw3232step1 := by
      have heq : raw3232step1 = (fun i j => raw3232step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3232step0 permutation31 permutation20
    _ = injectiveMoment H node943 := by rfl

def raw3233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -2, 0]]

def raw3233step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, 0, 3, -2], ![3, -1, -2, 0]]

def raw3233step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![1, 0, -3, 2], ![-3, 1, 2, 0]]

def raw3233step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical3233 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3233 = injectiveMoment H node1011 := by
  calc
    injectiveMoment H raw3233 = injectiveMoment H raw3233step0 := by
      have heq : raw3233step0 = raw3233.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3233).symm
    injectiveMoment H raw3233step0 = injectiveMoment H raw3233step1 := by
      have heq : raw3233step1 = -raw3233step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3233step0).symm
    injectiveMoment H raw3233step1 = injectiveMoment H raw3233step2 := by
      have heq : raw3233step2 = (fun i j => raw3233step1 (permutation15 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3233step1 permutation15 permutation19
    _ = injectiveMoment H node1011 := by rfl

def raw3234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3234step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical3234 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3234 = injectiveMoment H node1094 := by
  calc
    injectiveMoment H raw3234 = injectiveMoment H raw3234step0 := by
      have heq : raw3234step0 = (fun i j => raw3234 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3234 permutation22 permutation17
    _ = injectiveMoment H node1094 := by rfl

def raw3235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw3235step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 0, 2, -1], ![3, -1, -2, 0]]

def raw3235step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3235 = injectiveMoment H node1207 := by
  calc
    injectiveMoment H raw3235 = injectiveMoment H raw3235step0 := by
      have heq : raw3235step0 = raw3235.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3235).symm
    injectiveMoment H raw3235step0 = injectiveMoment H raw3235step1 := by
      have heq : raw3235step1 = (fun i j => raw3235step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3235step0 permutation31 permutation20
    _ = injectiveMoment H node1207 := by rfl

def raw3236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw3236step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 2, -1]]

def raw3236step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical3236 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3236 = injectiveMoment H node1282 := by
  calc
    injectiveMoment H raw3236 = injectiveMoment H raw3236step0 := by
      have heq : raw3236step0 = -raw3236 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3236).symm
    injectiveMoment H raw3236step0 = injectiveMoment H raw3236step1 := by
      have heq : raw3236step1 = (fun i j => raw3236step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3236step0 permutation19 permutation15
    _ = injectiveMoment H node1282 := by rfl

def raw3237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 3, -3]]

def raw3237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 1, -3, 3]]

def raw3237step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical3237 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3237 = injectiveMoment H node1282 := by
  calc
    injectiveMoment H raw3237 = injectiveMoment H raw3237step0 := by
      have heq : raw3237step0 = -raw3237 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3237).symm
    injectiveMoment H raw3237step0 = injectiveMoment H raw3237step1 := by
      have heq : raw3237step1 = (fun i j => raw3237step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3237step0 permutation17 permutation15
    _ = injectiveMoment H node1282 := by rfl

def raw3238 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3238step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical3238 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3238 = injectiveMoment H node1641 := by
  calc
    injectiveMoment H raw3238 = injectiveMoment H raw3238step0 := by
      have heq : raw3238step0 = (fun i j => raw3238 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3238 permutation40 permutation11
    _ = injectiveMoment H node1641 := by rfl

def raw3239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3239step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, 1, -1, 1], ![3, -2, 0, -1]]

def raw3239step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, -1, 1, -1], ![-3, 2, 0, 1]]

def raw3239step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical3239 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3239 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw3239 = injectiveMoment H raw3239step0 := by
      have heq : raw3239step0 = raw3239.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3239).symm
    injectiveMoment H raw3239step0 = injectiveMoment H raw3239step1 := by
      have heq : raw3239step1 = -raw3239step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3239step0).symm
    injectiveMoment H raw3239step1 = injectiveMoment H raw3239step2 := by
      have heq : raw3239step2 = (fun i j => raw3239step1 (permutation16 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3239step1 permutation16 permutation23
    _ = injectiveMoment H node1056 := by rfl

def raw3240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical3240 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3240 = injectiveMoment H node1686 := by
  calc
    injectiveMoment H raw3240 = injectiveMoment H raw3240step0 := by
      have heq : raw3240step0 = (fun i j => raw3240 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3240 permutation40 permutation11
    _ = injectiveMoment H node1686 := by rfl

def raw3241 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3241step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical3241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3241 = injectiveMoment H node490 := by
  calc
    injectiveMoment H raw3241 = injectiveMoment H raw3241step0 := by
      have heq : raw3241step0 = (fun i j => raw3241 (permutation10 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3241 permutation10 permutation11
    _ = injectiveMoment H node490 := by rfl

def raw3242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -2, 0]]

theorem canonical3242 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3242 = injectiveMoment H node598 := by
  rfl

def raw3243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw3243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, 0, -1, 2]]

def raw3243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical3243 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3243 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw3243 = injectiveMoment H raw3243step0 := by
      have heq : raw3243step0 = -raw3243 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3243).symm
    injectiveMoment H raw3243step0 = injectiveMoment H raw3243step1 := by
      have heq : raw3243step1 = (fun i j => raw3243step0 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3243step0 permutation19 permutation17
    _ = injectiveMoment H node995 := by rfl

def raw3244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw3244step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical3244 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3244 = injectiveMoment H node1081 := by
  calc
    injectiveMoment H raw3244 = injectiveMoment H raw3244step0 := by
      have heq : raw3244step0 = -raw3244 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3244).symm
    injectiveMoment H raw3244step0 = injectiveMoment H raw3244step1 := by
      have heq : raw3244step1 = (fun i j => raw3244step0 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3244step0 permutation19 permutation17
    _ = injectiveMoment H node1081 := by rfl

def raw3245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, -1, 2, -2]]

def raw3245step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -1, 2], ![-1, 0, 2, -1], ![-1, 1, -2, 2]]

def raw3245step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical3245 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3245 = injectiveMoment H node1248 := by
  calc
    injectiveMoment H raw3245 = injectiveMoment H raw3245step0 := by
      have heq : raw3245step0 = -raw3245 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3245).symm
    injectiveMoment H raw3245step0 = injectiveMoment H raw3245step1 := by
      have heq : raw3245step1 = (fun i j => raw3245step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3245step0 permutation17 permutation15
    _ = injectiveMoment H node1248 := by rfl

def raw3246 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw3246step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 1, -1]]

theorem canonical3246 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3246 = injectiveMoment H node594 := by
  calc
    injectiveMoment H raw3246 = injectiveMoment H raw3246step0 := by
      have heq : raw3246step0 = (fun i j => raw3246 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3246 permutation11 permutation9
    _ = injectiveMoment H node594 := by rfl

def raw3247 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3247step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, 2, -1, 0], ![3, -3, 0, 0]]

def raw3247step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

theorem canonical3247 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3247 = injectiveMoment H node1269 := by
  calc
    injectiveMoment H raw3247 = injectiveMoment H raw3247step0 := by
      have heq : raw3247step0 = raw3247.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3247).symm
    injectiveMoment H raw3247step0 = injectiveMoment H raw3247step1 := by
      have heq : raw3247step1 = (fun i j => raw3247step0 (permutation25 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3247step0 permutation25 permutation25
    _ = injectiveMoment H node1269 := by rfl

def raw3248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]

theorem canonical3248 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3248 = injectiveMoment H node599 := by
  rfl

def raw3249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw3249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical3249 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3249 = injectiveMoment H node797 := by
  calc
    injectiveMoment H raw3249 = injectiveMoment H raw3249step0 := by
      have heq : raw3249step0 = -raw3249 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3249).symm
    injectiveMoment H raw3249step0 = injectiveMoment H raw3249step1 := by
      have heq : raw3249step1 = (fun i j => raw3249step0 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3249step0 permutation19 permutation17
    _ = injectiveMoment H node797 := by rfl

def raw3250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 2, 0, -1], ![3, -3, 0, 0]]

def raw3250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![1, -2, 0, 1], ![-3, 3, 0, 0]]

def raw3250step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical3250 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3250 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw3250 = injectiveMoment H raw3250step0 := by
      have heq : raw3250step0 = raw3250.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3250).symm
    injectiveMoment H raw3250step0 = injectiveMoment H raw3250step1 := by
      have heq : raw3250step1 = -raw3250step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3250step0).symm
    injectiveMoment H raw3250step1 = injectiveMoment H raw3250step2 := by
      have heq : raw3250step2 = (fun i j => raw3250step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3250step1 permutation14 permutation26
    _ = injectiveMoment H node1063 := by rfl

def raw3251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -2, 3], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw3251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical3251 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3251 = injectiveMoment H node1209 := by
  calc
    injectiveMoment H raw3251 = injectiveMoment H raw3251step0 := by
      have heq : raw3251step0 = -raw3251 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3251).symm
    injectiveMoment H raw3251step0 = injectiveMoment H raw3251step1 := by
      have heq : raw3251step1 = (fun i j => raw3251step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3251step0 permutation19 permutation15
    _ = injectiveMoment H node1209 := by rfl

def raw3252 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw3252step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -2, 3], ![-1, 0, 2, -1], ![-1, 1, -1, 1]]

def raw3252step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical3252 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3252 = injectiveMoment H node1209 := by
  calc
    injectiveMoment H raw3252 = injectiveMoment H raw3252step0 := by
      have heq : raw3252step0 = -raw3252 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3252).symm
    injectiveMoment H raw3252step0 = injectiveMoment H raw3252step1 := by
      have heq : raw3252step1 = (fun i j => raw3252step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3252step0 permutation17 permutation15
    _ = injectiveMoment H node1209 := by rfl

def raw3253 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 1, -2, 0]]

theorem canonical3253 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3253 = injectiveMoment H node600 := by
  rfl

def raw3254 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3254step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 3, -1, -1], ![3, -4, 1, 0]]

def raw3254step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical3254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3254 = injectiveMoment H node934 := by
  calc
    injectiveMoment H raw3254 = injectiveMoment H raw3254step0 := by
      have heq : raw3254step0 = raw3254.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3254).symm
    injectiveMoment H raw3254step0 = injectiveMoment H raw3254step1 := by
      have heq : raw3254step1 = (fun i j => raw3254step0 (permutation24 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3254step0 permutation24 permutation31
    _ = injectiveMoment H node934 := by rfl

def raw3255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 3, 0, -2], ![3, -4, 0, 1]]

def raw3255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![1, -3, 0, 2], ![-3, 4, 0, -1]]

def raw3255step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical3255 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3255 = injectiveMoment H node1156 := by
  calc
    injectiveMoment H raw3255 = injectiveMoment H raw3255step0 := by
      have heq : raw3255step0 = raw3255.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3255).symm
    injectiveMoment H raw3255step0 = injectiveMoment H raw3255step1 := by
      have heq : raw3255step1 = -raw3255step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3255step0).symm
    injectiveMoment H raw3255step1 = injectiveMoment H raw3255step2 := by
      have heq : raw3255step2 = (fun i j => raw3255step1 (permutation14 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3255step1 permutation14 permutation25
    _ = injectiveMoment H node1156 := by rfl

def raw3256 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw3256step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-1, 3, -2, 0], ![3, -4, 1, 0]]

def raw3256step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![1, -3, 2, 0], ![-3, 4, -1, 0]]

def raw3256step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical3256 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3256 = injectiveMoment H node1156 := by
  calc
    injectiveMoment H raw3256 = injectiveMoment H raw3256step0 := by
      have heq : raw3256step0 = raw3256.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3256).symm
    injectiveMoment H raw3256step0 = injectiveMoment H raw3256step1 := by
      have heq : raw3256step1 = -raw3256step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3256step0).symm
    injectiveMoment H raw3256step1 = injectiveMoment H raw3256step2 := by
      have heq : raw3256step2 = (fun i j => raw3256step1 (permutation14 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3256step1 permutation14 permutation31
    _ = injectiveMoment H node1156 := by rfl

def raw3257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3257step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -2, 0, 3], ![3, 0, 1, -4]]

def raw3257step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical3257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3257 = injectiveMoment H node595 := by
  calc
    injectiveMoment H raw3257 = injectiveMoment H raw3257step0 := by
      have heq : raw3257step0 = raw3257.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3257).symm
    injectiveMoment H raw3257step0 = injectiveMoment H raw3257step1 := by
      have heq : raw3257step1 = (fun i j => raw3257step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3257step0 permutation22 permutation17
    _ = injectiveMoment H node595 := by rfl

def raw3258 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

theorem canonical3258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3258 = injectiveMoment H node601 := by
  rfl

def raw3259 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical3259 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3259 = injectiveMoment H node602 := by
  rfl

def raw3260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -2, 3, 0], ![3, 0, -2, -1]]

def raw3260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, 2, -3, 0], ![-3, 0, 2, 1]]

def raw3260step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical3260 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3260 = injectiveMoment H node1305 := by
  calc
    injectiveMoment H raw3260 = injectiveMoment H raw3260step0 := by
      have heq : raw3260step0 = raw3260.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3260).symm
    injectiveMoment H raw3260step0 = injectiveMoment H raw3260step1 := by
      have heq : raw3260step1 = -raw3260step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3260step0).symm
    injectiveMoment H raw3260step1 = injectiveMoment H raw3260step2 := by
      have heq : raw3260step2 = (fun i j => raw3260step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3260step1 permutation9 permutation29
    _ = injectiveMoment H node1305 := by rfl

def raw3261 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3261step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-1, -2, 0, 3], ![3, 0, 0, -3]]

def raw3261step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![1, 2, 0, -3], ![-3, 0, 0, 3]]

def raw3261step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical3261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3261 = injectiveMoment H node1313 := by
  calc
    injectiveMoment H raw3261 = injectiveMoment H raw3261step0 := by
      have heq : raw3261step0 = raw3261.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3261).symm
    injectiveMoment H raw3261step0 = injectiveMoment H raw3261step1 := by
      have heq : raw3261step1 = -raw3261step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3261step0).symm
    injectiveMoment H raw3261step1 = injectiveMoment H raw3261step2 := by
      have heq : raw3261step2 = (fun i j => raw3261step1 (permutation14 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3261step1 permutation14 permutation23
    _ = injectiveMoment H node1313 := by rfl

def raw3262 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical3262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3262 = injectiveMoment H node603 := by
  rfl

def raw3263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw3263step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical3263 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3263 = injectiveMoment H node603 := by
  calc
    injectiveMoment H raw3263 = injectiveMoment H raw3263step0 := by
      have heq : raw3263step0 = (fun i j => raw3263 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3263 permutation10 permutation9
    _ = injectiveMoment H node603 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
