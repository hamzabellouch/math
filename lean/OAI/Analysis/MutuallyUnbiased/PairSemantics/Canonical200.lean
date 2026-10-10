import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6400 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical6400 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6400 = injectiveMoment H node2579 := by
  rfl

def raw6401 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw6401step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 0, 1, -1], ![2, 1, -3, 0]]

def raw6401step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, -2, 0], ![0, 0, -1, 1], ![-2, -1, 3, 0]]

def raw6401step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6401 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6401 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw6401 = injectiveMoment H raw6401step0 := by
      have heq : raw6401step0 = raw6401.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6401).symm
    injectiveMoment H raw6401step0 = injectiveMoment H raw6401step1 := by
      have heq : raw6401step1 = -raw6401step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6401step0).symm
    injectiveMoment H raw6401step1 = injectiveMoment H raw6401step2 := by
      have heq : raw6401step2 = (fun i j => raw6401step1 (permutation28 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6401step1 permutation28 permutation19
    _ = injectiveMoment H node1202 := by rfl

def raw6402 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw6402step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 0, 2, -2], ![2, 1, -4, 1]]

def raw6402step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, -2, 0], ![0, 0, -2, 2], ![-2, -1, 4, -1]]

def raw6402step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical6402 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6402 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw6402 = injectiveMoment H raw6402step0 := by
      have heq : raw6402step0 = raw6402.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6402).symm
    injectiveMoment H raw6402step0 = injectiveMoment H raw6402step1 := by
      have heq : raw6402step1 = -raw6402step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6402step0).symm
    injectiveMoment H raw6402step1 = injectiveMoment H raw6402step2 := by
      have heq : raw6402step2 = (fun i j => raw6402step1 (permutation31 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6402step1 permutation31 permutation16
    _ = injectiveMoment H node771 := by rfl

def raw6403 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical6403 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6403 = injectiveMoment H node2580 := by
  rfl

def raw6404 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6404 = injectiveMoment H node2586 := by
  rfl

def raw6405 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw6405step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw6405step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem canonical6405 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6405 = injectiveMoment H node3340 := by
  calc
    injectiveMoment H raw6405 = injectiveMoment H raw6405step0 := by
      have heq : raw6405step0 = -raw6405 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6405).symm
    injectiveMoment H raw6405step0 = injectiveMoment H raw6405step1 := by
      have heq : raw6405step1 = (fun i j => raw6405step0 (permutation386 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6405step0 permutation386 permutation9
    _ = injectiveMoment H node3340 := by rfl

def raw6406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical6406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6406 = injectiveMoment H node1003 := by
  rfl

def raw6407 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -3, 2]]

theorem canonical6407 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6407 = injectiveMoment H node1004 := by
  rfl

def raw6408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical6408 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6408 = injectiveMoment H node1005 := by
  rfl

def raw6409 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6409 = injectiveMoment H node2587 := by
  rfl

def raw6410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6410 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6410 = injectiveMoment H node2588 := by
  rfl

def raw6411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical6411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6411 = injectiveMoment H node1006 := by
  rfl

def raw6412 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, -1, 2, 0]]

def raw6412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical6412 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6412 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw6412 = injectiveMoment H raw6412step0 := by
      have heq : raw6412step0 = -raw6412 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6412).symm
    injectiveMoment H raw6412step0 = injectiveMoment H raw6412step1 := by
      have heq : raw6412step1 = (fun i j => raw6412step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6412step0 permutation32 permutation10
    _ = injectiveMoment H node1000 := by rfl

def raw6413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -3, 1]]

def raw6413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, -2, 1], ![0, -1, -1, 2], ![-1, -1, 3, -1]]

def raw6413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical6413 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6413 = injectiveMoment H node943 := by
  calc
    injectiveMoment H raw6413 = injectiveMoment H raw6413step0 := by
      have heq : raw6413step0 = -raw6413 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6413).symm
    injectiveMoment H raw6413step0 = injectiveMoment H raw6413step1 := by
      have heq : raw6413step1 = (fun i j => raw6413step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6413step0 permutation32 permutation10
    _ = injectiveMoment H node943 := by rfl

def raw6414 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical6414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6414 = injectiveMoment H node1008 := by
  rfl

def raw6415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical6415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6415 = injectiveMoment H node1009 := by
  rfl

def raw6416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical6416 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6416 = injectiveMoment H node1010 := by
  rfl

def raw6417 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical6417 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6417 = injectiveMoment H node1011 := by
  rfl

def raw6418 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![1, 2, -2, -1]]

def raw6418step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]

def raw6418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, -2, 2], ![-2, 1, 1]]

def raw6418step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6418 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6418 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw6418 = injectiveMoment H raw6418step0 := by
      have heq : raw6418step0 = raw6418.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6418).symm
    injectiveMoment H raw6418step0 = injectiveMoment H raw6418step1 := by
      have heq : raw6418step1 = -raw6418step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6418step0).symm
    injectiveMoment H raw6418step1 = injectiveMoment H raw6418step2 := by
      have heq : raw6418step2 = (fun i j => raw6418step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6418step1 permutation22 permutation5
    _ = injectiveMoment H node210 := by rfl

def raw6419 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![1, 2, -3, 0]]

def raw6419step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![2, -2, 0]]

def raw6419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, -3, 3], ![-2, 2, 0]]

def raw6419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical6419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6419 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw6419 = injectiveMoment H raw6419step0 := by
      have heq : raw6419step0 = raw6419.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6419).symm
    injectiveMoment H raw6419step0 = injectiveMoment H raw6419step1 := by
      have heq : raw6419step1 = -raw6419step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6419step0).symm
    injectiveMoment H raw6419step1 = injectiveMoment H raw6419step2 := by
      have heq : raw6419step2 = (fun i j => raw6419step1 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6419step1 permutation32 permutation4
    _ = injectiveMoment H node215 := by rfl

def raw6420 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![1, 1, 3, -5]]

def raw6420step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3], ![2, 3, -5]]

def raw6420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 3, -3], ![-2, -3, 5]]

def raw6420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6420 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6420 = injectiveMoment H node129 := by
  calc
    injectiveMoment H raw6420 = injectiveMoment H raw6420step0 := by
      have heq : raw6420step0 = raw6420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6420).symm
    injectiveMoment H raw6420step0 = injectiveMoment H raw6420step1 := by
      have heq : raw6420step1 = -raw6420step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6420step0).symm
    injectiveMoment H raw6420step1 = injectiveMoment H raw6420step2 := by
      have heq : raw6420step2 = (fun i j => raw6420step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6420step1 permutation31 permutation3
    _ = injectiveMoment H node129 := by rfl

def raw6421 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6421step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw6421step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

theorem canonical6421 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6421 = injectiveMoment H node2320 := by
  calc
    injectiveMoment H raw6421 = injectiveMoment H raw6421step0 := by
      have heq : raw6421step0 = -raw6421 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6421).symm
    injectiveMoment H raw6421step0 = injectiveMoment H raw6421step1 := by
      have heq : raw6421step1 = (fun i j => raw6421step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6421step0 permutation101 permutation15
    _ = injectiveMoment H node2320 := by rfl

def raw6422 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![-1, 2, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6422step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 2, -2], ![1, -2, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw6422step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

theorem canonical6422 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6422 = injectiveMoment H node2258 := by
  calc
    injectiveMoment H raw6422 = injectiveMoment H raw6422step0 := by
      have heq : raw6422step0 = -raw6422 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6422).symm
    injectiveMoment H raw6422step0 = injectiveMoment H raw6422step1 := by
      have heq : raw6422step1 = (fun i j => raw6422step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6422step0 permutation101 permutation15
    _ = injectiveMoment H node2258 := by rfl

def raw6423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical6423 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6423 = injectiveMoment H node1028 := by
  rfl

def raw6424 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw6424step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6424 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6424 = injectiveMoment H node2590 := by
  calc
    injectiveMoment H raw6424 = injectiveMoment H raw6424step0 := by
      have heq : raw6424step0 = (fun i j => raw6424 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6424 permutation35 permutation9
    _ = injectiveMoment H node2590 := by rfl

def raw6425 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical6425 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6425 = injectiveMoment H node2592 := by
  rfl

def raw6426 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![0, 1, 0, -1]]

def raw6426step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6426 = injectiveMoment H node2591 := by
  calc
    injectiveMoment H raw6426 = injectiveMoment H raw6426step0 := by
      have heq : raw6426step0 = (fun i j => raw6426 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6426 permutation34 permutation9
    _ = injectiveMoment H node2591 := by rfl

def raw6427 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical6427 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6427 = injectiveMoment H node1031 := by
  rfl

def raw6428 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw6428step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6428 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6428 = injectiveMoment H node2590 := by
  calc
    injectiveMoment H raw6428 = injectiveMoment H raw6428step0 := by
      have heq : raw6428step0 = (fun i j => raw6428 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6428 permutation36 permutation15
    _ = injectiveMoment H node2590 := by rfl

def raw6429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![0, 1, -1, 0]]

def raw6429step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6429 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6429 = injectiveMoment H node2591 := by
  calc
    injectiveMoment H raw6429 = injectiveMoment H raw6429step0 := by
      have heq : raw6429step0 = (fun i j => raw6429 (permutation37 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6429 permutation37 permutation9
    _ = injectiveMoment H node2591 := by rfl

def raw6430 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical6430 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6430 = injectiveMoment H node1032 := by
  rfl

def raw6431 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw6431step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical6431 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6431 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw6431 = injectiveMoment H raw6431step0 := by
      have heq : raw6431step0 = (fun i j => raw6431 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6431 permutation10 permutation15
    _ = injectiveMoment H node1032 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
