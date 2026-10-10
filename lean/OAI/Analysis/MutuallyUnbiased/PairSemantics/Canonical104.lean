import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3328 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw3328step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical3328 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3328 = injectiveMoment H node2000 := by
  calc
    injectiveMoment H raw3328 = injectiveMoment H raw3328step0 := by
      have heq : raw3328step0 = (fun i j => raw3328 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3328 permutation34 permutation9
    _ = injectiveMoment H node2000 := by rfl

def raw3329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw3329step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3329step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3329 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3329 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw3329 = injectiveMoment H raw3329step0 := by
      have heq : raw3329step0 = raw3329.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3329).symm
    injectiveMoment H raw3329step0 = injectiveMoment H raw3329step1 := by
      have heq : raw3329step1 = (fun i j => raw3329step0 (permutation22 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3329step0 permutation22 permutation21
    _ = injectiveMoment H node1304 := by rfl

def raw3330 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical3330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3330 = injectiveMoment H node2001 := by
  rfl

def raw3331 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

theorem canonical3331 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3331 = injectiveMoment H node2002 := by
  rfl

def raw3332 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical3332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3332 = injectiveMoment H node2003 := by
  rfl

def raw3333 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3333step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 2, 0]]

def raw3333step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical3333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3333 = injectiveMoment H node1999 := by
  calc
    injectiveMoment H raw3333 = injectiveMoment H raw3333step0 := by
      have heq : raw3333step0 = -raw3333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3333).symm
    injectiveMoment H raw3333step0 = injectiveMoment H raw3333step1 := by
      have heq : raw3333step1 = (fun i j => raw3333step0 (permutation59 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3333step0 permutation59 permutation25
    _ = injectiveMoment H node1999 := by rfl

def raw3334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw3334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, -1, 2, 0], ![-1, 0, 0, 1]]

def raw3334step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical3334 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3334 = injectiveMoment H node1999 := by
  calc
    injectiveMoment H raw3334 = injectiveMoment H raw3334step0 := by
      have heq : raw3334step0 = -raw3334 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3334).symm
    injectiveMoment H raw3334step0 = injectiveMoment H raw3334step1 := by
      have heq : raw3334step1 = (fun i j => raw3334step0 (permutation61 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3334step0 permutation61 permutation25
    _ = injectiveMoment H node1999 := by rfl

def raw3335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw3335step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical3335 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3335 = injectiveMoment H node2003 := by
  calc
    injectiveMoment H raw3335 = injectiveMoment H raw3335step0 := by
      have heq : raw3335step0 = (fun i j => raw3335 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3335 permutation34 permutation9
    _ = injectiveMoment H node2003 := by rfl

def raw3336 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3336step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3336step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

theorem canonical3336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3336 = injectiveMoment H node1314 := by
  calc
    injectiveMoment H raw3336 = injectiveMoment H raw3336step0 := by
      have heq : raw3336step0 = raw3336.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3336).symm
    injectiveMoment H raw3336step0 = injectiveMoment H raw3336step1 := by
      have heq : raw3336step1 = (fun i j => raw3336step0 (permutation28 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3336step0 permutation28 permutation23
    _ = injectiveMoment H node1314 := by rfl

def raw3337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3337step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical3337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3337 = injectiveMoment H node1998 := by
  calc
    injectiveMoment H raw3337 = injectiveMoment H raw3337step0 := by
      have heq : raw3337step0 = (fun i j => raw3337 (permutation60 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3337 permutation60 permutation16
    _ = injectiveMoment H node1998 := by rfl

def raw3338 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical3338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3338 = injectiveMoment H node605 := by
  rfl

def raw3339 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3339 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3339 = injectiveMoment H node606 := by
  rfl

def raw3340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem canonical3340 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3340 = injectiveMoment H node2004 := by
  rfl

def raw3341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical3341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3341 = injectiveMoment H node2001 := by
  calc
    injectiveMoment H raw3341 = injectiveMoment H raw3341step0 := by
      have heq : raw3341step0 = (fun i j => raw3341 (permutation60 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3341 permutation60 permutation16
    _ = injectiveMoment H node2001 := by rfl

def raw3342 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical3342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3342 = injectiveMoment H node607 := by
  rfl

def raw3343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw3343step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw3343step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical3343 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3343 = injectiveMoment H node474 := by
  calc
    injectiveMoment H raw3343 = injectiveMoment H raw3343step0 := by
      have heq : raw3343step0 = -raw3343 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3343).symm
    injectiveMoment H raw3343step0 = injectiveMoment H raw3343step1 := by
      have heq : raw3343step1 = (fun i j => raw3343step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3343step0 permutation31 permutation15
    _ = injectiveMoment H node474 := by rfl

def raw3344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw3344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3344step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

theorem canonical3344 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3344 = injectiveMoment H node1314 := by
  calc
    injectiveMoment H raw3344 = injectiveMoment H raw3344step0 := by
      have heq : raw3344step0 = raw3344.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3344).symm
    injectiveMoment H raw3344step0 = injectiveMoment H raw3344step1 := by
      have heq : raw3344step1 = (fun i j => raw3344step0 (permutation24 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3344step0 permutation24 permutation21
    _ = injectiveMoment H node1314 := by rfl

def raw3345 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3345 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3345 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw3345 = injectiveMoment H raw3345step0 := by
      have heq : raw3345step0 = raw3345.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3345).symm
    injectiveMoment H raw3345step0 = injectiveMoment H raw3345step1 := by
      have heq : raw3345step1 = (fun i j => raw3345step0 (permutation30 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3345step0 permutation30 permutation23
    _ = injectiveMoment H node1304 := by rfl

def raw3346 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3346step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![-1, -1, 2, 0], ![-1, -1, 0, 2]]

def raw3346step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3346 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3346 = injectiveMoment H node606 := by
  calc
    injectiveMoment H raw3346 = injectiveMoment H raw3346step0 := by
      have heq : raw3346step0 = -raw3346 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3346).symm
    injectiveMoment H raw3346step0 = injectiveMoment H raw3346step1 := by
      have heq : raw3346step1 = (fun i j => raw3346step0 (permutation16 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3346step0 permutation16 permutation25
    _ = injectiveMoment H node606 := by rfl

def raw3347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical3347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3347 = injectiveMoment H node608 := by
  rfl

def raw3348 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 2, 0, -3], ![1, 0, -2, 1]]

def raw3348step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![-1, -2, 0, 3], ![-1, 0, 2, -1]]

def raw3348step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical3348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3348 = injectiveMoment H node474 := by
  calc
    injectiveMoment H raw3348 = injectiveMoment H raw3348step0 := by
      have heq : raw3348step0 = -raw3348 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3348).symm
    injectiveMoment H raw3348step0 = injectiveMoment H raw3348step1 := by
      have heq : raw3348step1 = (fun i j => raw3348step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3348step0 permutation25 permutation15
    _ = injectiveMoment H node474 := by rfl

def raw3349 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![2, 2, -2, -2]]

def raw3349step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical3349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3349 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw3349 = injectiveMoment H raw3349step0 := by
      have heq : raw3349step0 = raw3349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3349).symm
    _ = injectiveMoment H node197 := by rfl

def raw3350 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 3, -1], ![2, 2, -3, -1]]

def raw3350step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical3350 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3350 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw3350 = injectiveMoment H raw3350step0 := by
      have heq : raw3350step0 = raw3350.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3350).symm
    _ = injectiveMoment H node198 := by rfl

def raw3351 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 4, -2], ![2, 2, -4, 0]]

def raw3351step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

theorem canonical3351 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3351 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw3351 = injectiveMoment H raw3351step0 := by
      have heq : raw3351step0 = raw3351.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3351).symm
    _ = injectiveMoment H node199 := by rfl

def raw3352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3352step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, 0, 0, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3352step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3352step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical3352 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3352 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw3352 = injectiveMoment H raw3352step0 := by
      have heq : raw3352step0 = -raw3352 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3352).symm
    injectiveMoment H raw3352step0 = injectiveMoment H raw3352step1 := by
      have hz : ∀ j, raw3352step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3352step1 = (fun i j => raw3352step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3352step0 permutation80 hz
    injectiveMoment H raw3352step1 = injectiveMoment H raw3352step2 := by
      have heq : raw3352step2 = (fun i j => raw3352step1 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3352step1 permutation28 permutation17
    _ = injectiveMoment H node771 := by rfl

def raw3353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3353step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3353step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical3353 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3353 = injectiveMoment H node1562 := by
  calc
    injectiveMoment H raw3353 = injectiveMoment H raw3353step0 := by
      have heq : raw3353step0 = -raw3353 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3353).symm
    injectiveMoment H raw3353step0 = injectiveMoment H raw3353step1 := by
      have heq : raw3353step1 = (fun i j => raw3353step0 (permutation146 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3353step0 permutation146 permutation21
    _ = injectiveMoment H node1562 := by rfl

def raw3354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw3354step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical3354 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3354 = injectiveMoment H node2715 := by
  calc
    injectiveMoment H raw3354 = injectiveMoment H raw3354step0 := by
      have heq : raw3354step0 = (fun i j => raw3354 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3354 permutation60 permutation15
    _ = injectiveMoment H node2715 := by rfl

def raw3355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw3355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical3355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3355 = injectiveMoment H node1037 := by
  calc
    injectiveMoment H raw3355 = injectiveMoment H raw3355step0 := by
      have heq : raw3355step0 = (fun i j => raw3355 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3355 permutation16 permutation17
    _ = injectiveMoment H node1037 := by rfl

def raw3356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw3356step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical3356 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3356 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw3356 = injectiveMoment H raw3356step0 := by
      have heq : raw3356step0 = (fun i j => raw3356 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3356 permutation16 permutation17
    _ = injectiveMoment H node1027 := by rfl

def raw3357 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical3357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3357 = injectiveMoment H node2005 := by
  rfl

def raw3358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3358step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw3358step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical3358 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3358 = injectiveMoment H node2683 := by
  calc
    injectiveMoment H raw3358 = injectiveMoment H raw3358step0 := by
      have heq : raw3358step0 = -raw3358 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3358).symm
    injectiveMoment H raw3358step0 = injectiveMoment H raw3358step1 := by
      have heq : raw3358step1 = (fun i j => raw3358step0 (permutation96 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3358step0 permutation96 permutation15
    _ = injectiveMoment H node2683 := by rfl

def raw3359 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw3359step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-2, 0, 2, 0]]

def raw3359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical3359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3359 = injectiveMoment H node1164 := by
  calc
    injectiveMoment H raw3359 = injectiveMoment H raw3359step0 := by
      have heq : raw3359step0 = -raw3359 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3359).symm
    injectiveMoment H raw3359step0 = injectiveMoment H raw3359step1 := by
      have heq : raw3359step1 = (fun i j => raw3359step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3359step0 permutation25 permutation15
    _ = injectiveMoment H node1164 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
