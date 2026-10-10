import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7264 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw7264step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw7264step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical7264 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7264 = injectiveMoment H node2867 := by
  calc
    injectiveMoment H raw7264 = injectiveMoment H raw7264step0 := by
      have heq : raw7264step0 = -raw7264 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7264).symm
    injectiveMoment H raw7264step0 = injectiveMoment H raw7264step1 := by
      have heq : raw7264step1 = (fun i j => raw7264step0 (permutation326 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7264step0 permutation326 permutation23
    _ = injectiveMoment H node2867 := by rfl

def raw7265 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw7265step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw7265step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical7265 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7265 = injectiveMoment H node2921 := by
  calc
    injectiveMoment H raw7265 = injectiveMoment H raw7265step0 := by
      have heq : raw7265step0 = -raw7265 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7265).symm
    injectiveMoment H raw7265step0 = injectiveMoment H raw7265step1 := by
      have heq : raw7265step1 = (fun i j => raw7265step0 (permutation396 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7265step0 permutation396 permutation21
    _ = injectiveMoment H node2921 := by rfl

def raw7266 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw7266step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -2, 4]]

def raw7266step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical7266 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7266 = injectiveMoment H node2879 := by
  calc
    injectiveMoment H raw7266 = injectiveMoment H raw7266step0 := by
      have heq : raw7266step0 = -raw7266 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7266).symm
    injectiveMoment H raw7266step0 = injectiveMoment H raw7266step1 := by
      have heq : raw7266step1 = (fun i j => raw7266step0 (permutation328 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7266step0 permutation328 permutation17
    _ = injectiveMoment H node2879 := by rfl

def raw7267 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw7267step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw7267step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical7267 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7267 = injectiveMoment H node2974 := by
  calc
    injectiveMoment H raw7267 = injectiveMoment H raw7267step0 := by
      have heq : raw7267step0 = -raw7267 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7267).symm
    injectiveMoment H raw7267step0 = injectiveMoment H raw7267step1 := by
      have heq : raw7267step1 = (fun i j => raw7267step0 (permutation395 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7267step0 permutation395 permutation21
    _ = injectiveMoment H node2974 := by rfl

def raw7268 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7268step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -1, -2, 3]]

def raw7268step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical7268 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7268 = injectiveMoment H node3014 := by
  calc
    injectiveMoment H raw7268 = injectiveMoment H raw7268step0 := by
      have heq : raw7268step0 = -raw7268 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7268).symm
    injectiveMoment H raw7268step0 = injectiveMoment H raw7268step1 := by
      have heq : raw7268step1 = (fun i j => raw7268step0 (permutation320 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7268step0 permutation320 permutation23
    _ = injectiveMoment H node3014 := by rfl

def raw7269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw7269step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

theorem canonical7269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7269 = injectiveMoment H node2846 := by
  calc
    injectiveMoment H raw7269 = injectiveMoment H raw7269step0 := by
      have heq : raw7269step0 = (fun i j => raw7269 (permutation60 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7269 permutation60 permutation17
    _ = injectiveMoment H node2846 := by rfl

def raw7270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

theorem canonical7270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7270 = injectiveMoment H node1349 := by
  calc
    injectiveMoment H raw7270 = injectiveMoment H raw7270step0 := by
      have heq : raw7270step0 = (fun i j => raw7270 (permutation15 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7270 permutation15 permutation17
    _ = injectiveMoment H node1349 := by rfl

def raw7271 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7271step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -2, -2, 4]]

def raw7271step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical7271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7271 = injectiveMoment H node2878 := by
  calc
    injectiveMoment H raw7271 = injectiveMoment H raw7271step0 := by
      have heq : raw7271step0 = -raw7271 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7271).symm
    injectiveMoment H raw7271step0 = injectiveMoment H raw7271step1 := by
      have heq : raw7271step1 = (fun i j => raw7271step0 (permutation325 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7271step0 permutation325 permutation23
    _ = injectiveMoment H node2878 := by rfl

def raw7272 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7272step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -1, -2, 3]]

def raw7272step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical7272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7272 = injectiveMoment H node3011 := by
  calc
    injectiveMoment H raw7272 = injectiveMoment H raw7272step0 := by
      have heq : raw7272step0 = -raw7272 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7272).symm
    injectiveMoment H raw7272step0 = injectiveMoment H raw7272step1 := by
      have heq : raw7272step1 = (fun i j => raw7272step0 (permutation325 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7272step0 permutation325 permutation23
    _ = injectiveMoment H node3011 := by rfl

def raw7273 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7273step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7273 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7273 = injectiveMoment H node3404 := by
  calc
    injectiveMoment H raw7273 = injectiveMoment H raw7273step0 := by
      have heq : raw7273step0 = (fun i j => raw7273 (permutation401 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7273 permutation401 permutation30
    _ = injectiveMoment H node3404 := by rfl

def raw7274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw7274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, -2, 3, -1], ![1, 2, -3, 0]]

def raw7274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, 2, -3, 1], ![-1, -2, 3, 0]]

def raw7274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical7274 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7274 = injectiveMoment H node1217 := by
  calc
    injectiveMoment H raw7274 = injectiveMoment H raw7274step0 := by
      have heq : raw7274step0 = raw7274.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7274).symm
    injectiveMoment H raw7274step0 = injectiveMoment H raw7274step1 := by
      have heq : raw7274step1 = -raw7274step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7274step0).symm
    injectiveMoment H raw7274step1 = injectiveMoment H raw7274step2 := by
      have heq : raw7274step2 = (fun i j => raw7274step1 (permutation30 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7274step1 permutation30 permutation13
    _ = injectiveMoment H node1217 := by rfl

def raw7275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw7275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, -1, 3, -2], ![1, 1, -3, 1]]

def raw7275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![-1, -1, 3, -1]]

def raw7275step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical7275 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7275 = injectiveMoment H node933 := by
  calc
    injectiveMoment H raw7275 = injectiveMoment H raw7275step0 := by
      have heq : raw7275step0 = raw7275.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7275).symm
    injectiveMoment H raw7275step0 = injectiveMoment H raw7275step1 := by
      have heq : raw7275step1 = -raw7275step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7275step0).symm
    injectiveMoment H raw7275step1 = injectiveMoment H raw7275step2 := by
      have heq : raw7275step2 = (fun i j => raw7275step1 (permutation30 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7275step1 permutation30 permutation10
    _ = injectiveMoment H node933 := by rfl

def raw7276 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -3, 3, 0], ![1, 3, -3, -1]]

def raw7276step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7276 = injectiveMoment H node289 := by
  calc
    injectiveMoment H raw7276 = injectiveMoment H raw7276step0 := by
      have heq : raw7276step0 = raw7276.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7276).symm
    _ = injectiveMoment H node289 := by rfl

def raw7277 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -3, 4, -1], ![1, 3, -4, 0]]

def raw7277step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7277 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7277 = injectiveMoment H node290 := by
  calc
    injectiveMoment H raw7277 = injectiveMoment H raw7277step0 := by
      have heq : raw7277step0 = raw7277.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7277).symm
    _ = injectiveMoment H node290 := by rfl

def raw7278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 2, -1, -1], ![0, -1, -1, 2], ![-1, -1, 2, 0]]

def raw7278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical7278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7278 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw7278 = injectiveMoment H raw7278step0 := by
      have heq : raw7278step0 = -raw7278 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7278).symm
    injectiveMoment H raw7278step0 = injectiveMoment H raw7278step1 := by
      have heq : raw7278step1 = (fun i j => raw7278step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7278step0 permutation32 permutation10
    _ = injectiveMoment H node1009 := by rfl

def raw7279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw7279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 2, -1, -1], ![0, -2, 2, 0], ![-1, 0, -1, 2]]

def raw7279step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical7279 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7279 = injectiveMoment H node1008 := by
  calc
    injectiveMoment H raw7279 = injectiveMoment H raw7279step0 := by
      have heq : raw7279step0 = -raw7279 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7279).symm
    injectiveMoment H raw7279step0 = injectiveMoment H raw7279step1 := by
      have heq : raw7279step1 = (fun i j => raw7279step0 (permutation30 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7279step0 permutation30 permutation11
    _ = injectiveMoment H node1008 := by rfl

def raw7280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw7280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 2, -2, 0], ![0, -2, 0, 2], ![-1, 0, 2, -1]]

def raw7280step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical7280 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7280 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw7280 = injectiveMoment H raw7280step0 := by
      have heq : raw7280step0 = -raw7280 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7280).symm
    injectiveMoment H raw7280step0 = injectiveMoment H raw7280step1 := by
      have heq : raw7280step1 = (fun i j => raw7280step0 (permutation30 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7280step0 permutation30 permutation13
    _ = injectiveMoment H node1057 := by rfl

def raw7281 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![1, 2, -2, -1]]

def raw7281step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7281 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7281 = injectiveMoment H raw7281step0 := by
      have heq : raw7281step0 = raw7281.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7281).symm
    _ = injectiveMoment H node291 := by rfl

def raw7282 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 3, -1], ![1, 2, -3, 0]]

def raw7282step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7282 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7282 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw7282 = injectiveMoment H raw7282step0 := by
      have heq : raw7282step0 = raw7282.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7282).symm
    _ = injectiveMoment H node292 := by rfl

def raw7283 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 4, -2], ![1, 2, -4, 1]]

def raw7283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1]]

def raw7283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -4, 4], ![-1, 2, -1]]

def raw7283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7283 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw7283 = injectiveMoment H raw7283step0 := by
      have heq : raw7283step0 = raw7283.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7283).symm
    injectiveMoment H raw7283step0 = injectiveMoment H raw7283step1 := by
      have heq : raw7283step1 = -raw7283step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7283step0).symm
    injectiveMoment H raw7283step1 = injectiveMoment H raw7283step2 := by
      have heq : raw7283step2 = (fun i j => raw7283step1 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7283step1 permutation30 permutation4
    _ = injectiveMoment H node281 := by rfl

def raw7284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw7284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical7284 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7284 = injectiveMoment H node1197 := by
  calc
    injectiveMoment H raw7284 = injectiveMoment H raw7284step0 := by
      have heq : raw7284step0 = (fun i j => raw7284 (permutation16 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7284 permutation16 permutation15
    _ = injectiveMoment H node1197 := by rfl

def raw7285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw7285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 2, -3], ![0, -1, -3, 4], ![-1, 0, 1, 0]]

def raw7285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical7285 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7285 = injectiveMoment H node1167 := by
  calc
    injectiveMoment H raw7285 = injectiveMoment H raw7285step0 := by
      have heq : raw7285step0 = -raw7285 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7285).symm
    injectiveMoment H raw7285step0 = injectiveMoment H raw7285step1 := by
      have heq : raw7285step1 = (fun i j => raw7285step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7285step0 permutation25 permutation15
    _ = injectiveMoment H node1167 := by rfl

def raw7286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw7286step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 1, -2], ![0, -1, 2, -1], ![-1, 0, -3, 4]]

def raw7286step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical7286 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7286 = injectiveMoment H node1171 := by
  calc
    injectiveMoment H raw7286 = injectiveMoment H raw7286step0 := by
      have heq : raw7286step0 = -raw7286 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7286).symm
    injectiveMoment H raw7286step0 = injectiveMoment H raw7286step1 := by
      have heq : raw7286step1 = (fun i j => raw7286step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7286step0 permutation32 permutation9
    _ = injectiveMoment H node1171 := by rfl

def raw7287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw7287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 0, -2, 3]]

def raw7287step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical7287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7287 = injectiveMoment H node1203 := by
  calc
    injectiveMoment H raw7287 = injectiveMoment H raw7287step0 := by
      have heq : raw7287step0 = -raw7287 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7287).symm
    injectiveMoment H raw7287step0 = injectiveMoment H raw7287step1 := by
      have heq : raw7287step1 = (fun i j => raw7287step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7287step0 permutation32 permutation9
    _ = injectiveMoment H node1203 := by rfl

def raw7288 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical7288 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7288 = injectiveMoment H node1039 := by
  calc
    injectiveMoment H raw7288 = injectiveMoment H raw7288step0 := by
      have heq : raw7288step0 = (fun i j => raw7288 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7288 permutation16 permutation17
    _ = injectiveMoment H node1039 := by rfl

def raw7289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw7289step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-1, 0, 2, -1]]

def raw7289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical7289 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7289 = injectiveMoment H node1170 := by
  calc
    injectiveMoment H raw7289 = injectiveMoment H raw7289step0 := by
      have heq : raw7289step0 = -raw7289 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7289).symm
    injectiveMoment H raw7289step0 = injectiveMoment H raw7289step1 := by
      have heq : raw7289step1 = (fun i j => raw7289step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7289step0 permutation25 permutation15
    _ = injectiveMoment H node1170 := by rfl

def raw7290 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw7290step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, 0, -2], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw7290step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical7290 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7290 = injectiveMoment H node2938 := by
  calc
    injectiveMoment H raw7290 = injectiveMoment H raw7290step0 := by
      have heq : raw7290step0 = -raw7290 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7290).symm
    injectiveMoment H raw7290step0 = injectiveMoment H raw7290step1 := by
      have heq : raw7290step1 = (fun i j => raw7290step0 (permutation332 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7290step0 permutation332 permutation21
    _ = injectiveMoment H node2938 := by rfl

def raw7291 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw7291step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw7291step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical7291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7291 = injectiveMoment H node2914 := by
  calc
    injectiveMoment H raw7291 = injectiveMoment H raw7291step0 := by
      have heq : raw7291step0 = -raw7291 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7291).symm
    injectiveMoment H raw7291step0 = injectiveMoment H raw7291step1 := by
      have heq : raw7291step1 = (fun i j => raw7291step0 (permutation407 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7291step0 permutation407 permutation9
    _ = injectiveMoment H node2914 := by rfl

def raw7292 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw7292step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw7292step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical7292 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7292 = injectiveMoment H node3012 := by
  calc
    injectiveMoment H raw7292 = injectiveMoment H raw7292step0 := by
      have heq : raw7292step0 = -raw7292 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7292).symm
    injectiveMoment H raw7292step0 = injectiveMoment H raw7292step1 := by
      have heq : raw7292step1 = (fun i j => raw7292step0 (permutation348 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7292step0 permutation348 permutation11
    _ = injectiveMoment H node3012 := by rfl

def raw7293 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw7293step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw7293step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical7293 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7293 = injectiveMoment H node3354 := by
  calc
    injectiveMoment H raw7293 = injectiveMoment H raw7293step0 := by
      have heq : raw7293step0 = -raw7293 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7293).symm
    injectiveMoment H raw7293step0 = injectiveMoment H raw7293step1 := by
      have heq : raw7293step1 = (fun i j => raw7293step0 (permutation407 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7293step0 permutation407 permutation9
    _ = injectiveMoment H node3354 := by rfl

def raw7294 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw7294step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw7294step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical7294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7294 = injectiveMoment H node2866 := by
  calc
    injectiveMoment H raw7294 = injectiveMoment H raw7294step0 := by
      have heq : raw7294step0 = -raw7294 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7294).symm
    injectiveMoment H raw7294step0 = injectiveMoment H raw7294step1 := by
      have heq : raw7294step1 = (fun i j => raw7294step0 (permutation327 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7294step0 permutation327 permutation23
    _ = injectiveMoment H node2866 := by rfl

def raw7295 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw7295step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw7295step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical7295 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7295 = injectiveMoment H node2913 := by
  calc
    injectiveMoment H raw7295 = injectiveMoment H raw7295step0 := by
      have heq : raw7295step0 = -raw7295 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7295).symm
    injectiveMoment H raw7295step0 = injectiveMoment H raw7295step1 := by
      have heq : raw7295step1 = (fun i j => raw7295step0 (permutation399 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7295step0 permutation399 permutation21
    _ = injectiveMoment H node2913 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
