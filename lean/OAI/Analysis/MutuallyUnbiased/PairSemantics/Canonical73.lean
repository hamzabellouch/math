import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2336 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw2336step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical2336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2336 = injectiveMoment H node2447 := by
  calc
    injectiveMoment H raw2336 = injectiveMoment H raw2336step0 := by
      have heq : raw2336step0 = (fun i j => raw2336 (permutation38 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2336 permutation38 permutation15
    _ = injectiveMoment H node2447 := by rfl

def raw2337 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw2337step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2337step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical2337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2337 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2337 = injectiveMoment H raw2337step0 := by
      have heq : raw2337step0 = raw2337.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2337).symm
    injectiveMoment H raw2337step0 = injectiveMoment H raw2337step1 := by
      have heq : raw2337step1 = (fun i j => raw2337step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2337step0 permutation28 permutation24
    _ = injectiveMoment H node1053 := by rfl

def raw2338 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

theorem canonical2338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2338 = injectiveMoment H node1795 := by
  rfl

def raw2339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem canonical2339 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2339 = injectiveMoment H node1796 := by
  rfl

def raw2340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical2340 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2340 = injectiveMoment H node1797 := by
  rfl

def raw2341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2341 = injectiveMoment H node1798 := by
  rfl

def raw2342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical2342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2342 = injectiveMoment H node1799 := by
  rfl

def raw2343 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2343 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2343 = injectiveMoment H node1800 := by
  rfl

def raw2344 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2344step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical2344 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2344 = injectiveMoment H node1848 := by
  calc
    injectiveMoment H raw2344 = injectiveMoment H raw2344step0 := by
      have heq : raw2344step0 = (fun i j => raw2344 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2344 permutation33 permutation10
    _ = injectiveMoment H node1848 := by rfl

def raw2345 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw2345step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2345 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2345 = injectiveMoment H node1800 := by
  calc
    injectiveMoment H raw2345 = injectiveMoment H raw2345step0 := by
      have heq : raw2345step0 = (fun i j => raw2345 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2345 permutation34 permutation9
    _ = injectiveMoment H node1800 := by rfl

def raw2346 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw2346step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, 1, -2, 0], ![2, -1, 0, -1]]

def raw2346step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical2346 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2346 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw2346 = injectiveMoment H raw2346step0 := by
      have heq : raw2346step0 = raw2346.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2346).symm
    injectiveMoment H raw2346step0 = injectiveMoment H raw2346step1 := by
      have heq : raw2346step1 = (fun i j => raw2346step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2346step0 permutation29 permutation20
    _ = injectiveMoment H node1010 := by rfl

def raw2347 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical2347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2347 = injectiveMoment H node1801 := by
  rfl

def raw2348 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2348step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2348step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical2348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2348 = injectiveMoment H node1793 := by
  calc
    injectiveMoment H raw2348 = injectiveMoment H raw2348step0 := by
      have heq : raw2348step0 = -raw2348 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2348).symm
    injectiveMoment H raw2348step0 = injectiveMoment H raw2348step1 := by
      have heq : raw2348step1 = (fun i j => raw2348step0 (permutation49 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2348step0 permutation49 permutation32
    _ = injectiveMoment H node1793 := by rfl

def raw2349 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw2349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, 1, -1, -1], ![2, -1, -1, 0]]

def raw2349step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical2349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2349 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw2349 = injectiveMoment H raw2349step0 := by
      have heq : raw2349step0 = raw2349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2349).symm
    injectiveMoment H raw2349step0 = injectiveMoment H raw2349step1 := by
      have heq : raw2349step1 = (fun i j => raw2349step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2349step0 permutation27 permutation18
    _ = injectiveMoment H node1058 := by rfl

def raw2350 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

theorem canonical2350 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2350 = injectiveMoment H node1802 := by
  rfl

def raw2351 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2351 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2351 = injectiveMoment H node1803 := by
  rfl

def raw2352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical2352 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2352 = injectiveMoment H node1804 := by
  rfl

def raw2353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2353step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2353 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2353 = injectiveMoment H node1803 := by
  calc
    injectiveMoment H raw2353 = injectiveMoment H raw2353step0 := by
      have heq : raw2353step0 = (fun i j => raw2353 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2353 permutation34 permutation9
    _ = injectiveMoment H node1803 := by rfl

def raw2354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

theorem canonical2354 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2354 = injectiveMoment H node1805 := by
  rfl

def raw2355 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

theorem canonical2355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2355 = injectiveMoment H node1806 := by
  rfl

def raw2356 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

theorem canonical2356 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2356 = injectiveMoment H node1807 := by
  rfl

def raw2357 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw2357step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![1, 1, -1, -1], ![2, -1, 1, -2]]

def raw2357step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical2357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2357 = injectiveMoment H node1333 := by
  calc
    injectiveMoment H raw2357 = injectiveMoment H raw2357step0 := by
      have heq : raw2357step0 = raw2357.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2357).symm
    injectiveMoment H raw2357step0 = injectiveMoment H raw2357step1 := by
      have heq : raw2357step1 = (fun i j => raw2357step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2357step0 permutation29 permutation18
    _ = injectiveMoment H node1333 := by rfl

def raw2358 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw2358step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![1, 1, 0, -2], ![2, -1, 0, -1]]

def raw2358step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

theorem canonical2358 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2358 = injectiveMoment H node1247 := by
  calc
    injectiveMoment H raw2358 = injectiveMoment H raw2358step0 := by
      have heq : raw2358step0 = raw2358.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2358).symm
    injectiveMoment H raw2358step0 = injectiveMoment H raw2358step1 := by
      have heq : raw2358step1 = (fun i j => raw2358step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2358step0 permutation29 permutation18
    _ = injectiveMoment H node1247 := by rfl

def raw2359 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw2359step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![2, -1, 0, -1]]

def raw2359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-2, 1, 0, 1]]

def raw2359step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2359 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw2359 = injectiveMoment H raw2359step0 := by
      have heq : raw2359step0 = raw2359.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2359).symm
    injectiveMoment H raw2359step0 = injectiveMoment H raw2359step1 := by
      have heq : raw2359step1 = -raw2359step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2359step0).symm
    injectiveMoment H raw2359step1 = injectiveMoment H raw2359step2 := by
      have heq : raw2359step2 = (fun i j => raw2359step1 (permutation10 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2359step1 permutation10 permutation24
    _ = injectiveMoment H node1260 := by rfl

def raw2360 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw2360step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2360step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical2360 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2360 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw2360 = injectiveMoment H raw2360step0 := by
      have heq : raw2360step0 = raw2360.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2360).symm
    injectiveMoment H raw2360step0 = injectiveMoment H raw2360step1 := by
      have heq : raw2360step1 = (fun i j => raw2360step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2360step0 permutation30 permutation24
    _ = injectiveMoment H node1047 := by rfl

def raw2361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical2361 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2361 = injectiveMoment H node1808 := by
  rfl

def raw2362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical2362 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2362 = injectiveMoment H node1809 := by
  rfl

def raw2363 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 0, -1, -1]]

def raw2363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2363 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2363 = injectiveMoment H node844 := by
  calc
    injectiveMoment H raw2363 = injectiveMoment H raw2363step0 := by
      have heq : raw2363step0 = (fun i j => raw2363 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2363 permutation10 permutation15
    _ = injectiveMoment H node844 := by rfl

def raw2364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw2364step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical2364 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2364 = injectiveMoment H node1808 := by
  calc
    injectiveMoment H raw2364 = injectiveMoment H raw2364step0 := by
      have heq : raw2364step0 = (fun i j => raw2364 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2364 permutation35 permutation9
    _ = injectiveMoment H node1808 := by rfl

def raw2365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw2365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical2365 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2365 = injectiveMoment H node1843 := by
  calc
    injectiveMoment H raw2365 = injectiveMoment H raw2365step0 := by
      have heq : raw2365step0 = (fun i j => raw2365 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2365 permutation33 permutation10
    _ = injectiveMoment H node1843 := by rfl

def raw2366 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem canonical2366 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2366 = injectiveMoment H node1810 := by
  rfl

def raw2367 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical2367 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2367 = injectiveMoment H node1811 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
