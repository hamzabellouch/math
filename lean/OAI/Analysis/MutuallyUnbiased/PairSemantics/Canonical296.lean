import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9472 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1], ![-2, -1, 2, 1]]

def raw9472step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9472 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9472 = injectiveMoment H node3062 := by
  calc
    injectiveMoment H raw9472 = injectiveMoment H raw9472step0 := by
      have heq : raw9472step0 = (fun i j => raw9472 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9472 permutation331 permutation10
    _ = injectiveMoment H node3062 := by rfl

def raw9473 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 1, 2]]

def raw9473step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical9473 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9473 = injectiveMoment H node3060 := by
  calc
    injectiveMoment H raw9473 = injectiveMoment H raw9473step0 := by
      have heq : raw9473step0 = (fun i j => raw9473 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9473 permutation308 permutation9
    _ = injectiveMoment H node3060 := by rfl

def raw9474 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9474step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical9474 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9474 = injectiveMoment H node3032 := by
  calc
    injectiveMoment H raw9474 = injectiveMoment H raw9474step0 := by
      have heq : raw9474step0 = (fun i j => raw9474 (permutation343 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9474 permutation343 permutation19
    _ = injectiveMoment H node3032 := by rfl

def raw9475 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9475step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical9475 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9475 = injectiveMoment H node3259 := by
  calc
    injectiveMoment H raw9475 = injectiveMoment H raw9475step0 := by
      have heq : raw9475step0 = (fun i j => raw9475 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9475 permutation259 permutation9
    _ = injectiveMoment H node3259 := by rfl

def raw9476 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def raw9476step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical9476 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9476 = injectiveMoment H node3198 := by
  calc
    injectiveMoment H raw9476 = injectiveMoment H raw9476step0 := by
      have heq : raw9476step0 = (fun i j => raw9476 (permutation283 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9476 permutation283 permutation12
    _ = injectiveMoment H node3198 := by rfl

def raw9477 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9477step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem canonical9477 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9477 = injectiveMoment H node2986 := by
  calc
    injectiveMoment H raw9477 = injectiveMoment H raw9477step0 := by
      have heq : raw9477step0 = (fun i j => raw9477 (permutation260 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9477 permutation260 permutation9
    _ = injectiveMoment H node2986 := by rfl

def raw9478 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def raw9478step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9478step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9478 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9478 = injectiveMoment H node3090 := by
  calc
    injectiveMoment H raw9478 = injectiveMoment H raw9478step0 := by
      have heq : raw9478step0 = -raw9478 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9478).symm
    injectiveMoment H raw9478step0 = injectiveMoment H raw9478step1 := by
      have heq : raw9478step1 = (fun i j => raw9478step0 (permutation339 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9478step0 permutation339 permutation11
    _ = injectiveMoment H node3090 := by rfl

def raw9479 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def raw9479step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, 2, 0, 0]]

def raw9479step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9479 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9479 = injectiveMoment H node3173 := by
  calc
    injectiveMoment H raw9479 = injectiveMoment H raw9479step0 := by
      have heq : raw9479step0 = -raw9479 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9479).symm
    injectiveMoment H raw9479step0 = injectiveMoment H raw9479step1 := by
      have heq : raw9479step1 = (fun i j => raw9479step0 (permutation337 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9479step0 permutation337 permutation12
    _ = injectiveMoment H node3173 := by rfl

def raw9480 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def raw9480step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, 2, 1, -1]]

def raw9480step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9480 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9480 = injectiveMoment H node3090 := by
  calc
    injectiveMoment H raw9480 = injectiveMoment H raw9480step0 := by
      have heq : raw9480step0 = -raw9480 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9480).symm
    injectiveMoment H raw9480step0 = injectiveMoment H raw9480step1 := by
      have heq : raw9480step1 = (fun i j => raw9480step0 (permutation322 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9480step0 permutation322 permutation13
    _ = injectiveMoment H node3090 := by rfl

def raw9481 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9481step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical9481 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9481 = injectiveMoment H node3057 := by
  calc
    injectiveMoment H raw9481 = injectiveMoment H raw9481step0 := by
      have heq : raw9481step0 = (fun i j => raw9481 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9481 permutation331 permutation10
    _ = injectiveMoment H node3057 := by rfl

def raw9482 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9482step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical9482 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9482 = injectiveMoment H node3057 := by
  calc
    injectiveMoment H raw9482 = injectiveMoment H raw9482step0 := by
      have heq : raw9482step0 = (fun i j => raw9482 (permutation310 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9482 permutation310 permutation9
    _ = injectiveMoment H node3057 := by rfl

def raw9483 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9483step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9483 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9483 = injectiveMoment H node2893 := by
  calc
    injectiveMoment H raw9483 = injectiveMoment H raw9483step0 := by
      have heq : raw9483step0 = (fun i j => raw9483 (permutation310 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9483 permutation310 permutation9
    _ = injectiveMoment H node2893 := by rfl

def raw9484 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def raw9484step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9484 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9484 = injectiveMoment H node2884 := by
  calc
    injectiveMoment H raw9484 = injectiveMoment H raw9484step0 := by
      have heq : raw9484step0 = (fun i j => raw9484 (permutation310 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9484 permutation310 permutation9
    _ = injectiveMoment H node2884 := by rfl

def raw9485 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, -1, 4], ![2, -1, 1, -2]]

def raw9485step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem canonical9485 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9485 = injectiveMoment H node2895 := by
  calc
    injectiveMoment H raw9485 = injectiveMoment H raw9485step0 := by
      have heq : raw9485step0 = (fun i j => raw9485 (permutation266 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9485 permutation266 permutation11
    _ = injectiveMoment H node2895 := by rfl

def raw9486 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 0, -1]]

def raw9486step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical9486 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9486 = injectiveMoment H node3422 := by
  calc
    injectiveMoment H raw9486 = injectiveMoment H raw9486step0 := by
      have heq : raw9486step0 = (fun i j => raw9486 (permutation189 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9486 permutation189 permutation21
    _ = injectiveMoment H node3422 := by rfl

def raw9487 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9487step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical9487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9487 = injectiveMoment H node2944 := by
  calc
    injectiveMoment H raw9487 = injectiveMoment H raw9487step0 := by
      have heq : raw9487step0 = (fun i j => raw9487 (permutation266 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9487 permutation266 permutation11
    _ = injectiveMoment H node2944 := by rfl

def raw9488 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 0, 0]]

def raw9488step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical9488 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9488 = injectiveMoment H node3425 := by
  calc
    injectiveMoment H raw9488 = injectiveMoment H raw9488step0 := by
      have heq : raw9488step0 = (fun i j => raw9488 (permutation189 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9488 permutation189 permutation21
    _ = injectiveMoment H node3425 := by rfl

def raw9489 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, -1, 1]]

def raw9489step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9489 = injectiveMoment H node3096 := by
  calc
    injectiveMoment H raw9489 = injectiveMoment H raw9489step0 := by
      have heq : raw9489step0 = (fun i j => raw9489 (permutation326 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9489 permutation326 permutation17
    _ = injectiveMoment H node3096 := by rfl

def raw9490 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -2, 2]]

def raw9490step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical9490 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9490 = injectiveMoment H node3181 := by
  calc
    injectiveMoment H raw9490 = injectiveMoment H raw9490step0 := by
      have heq : raw9490step0 = (fun i j => raw9490 (permutation277 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9490 permutation277 permutation10
    _ = injectiveMoment H node3181 := by rfl

def raw9491 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1], ![-2, -1, 2, 1]]

def raw9491step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical9491 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9491 = injectiveMoment H node3056 := by
  calc
    injectiveMoment H raw9491 = injectiveMoment H raw9491step0 := by
      have heq : raw9491step0 = (fun i j => raw9491 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9491 permutation331 permutation10
    _ = injectiveMoment H node3056 := by rfl

def raw9492 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 1, 2]]

def raw9492step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9492 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9492 = injectiveMoment H node3061 := by
  calc
    injectiveMoment H raw9492 = injectiveMoment H raw9492step0 := by
      have heq : raw9492step0 = (fun i j => raw9492 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9492 permutation308 permutation9
    _ = injectiveMoment H node3061 := by rfl

def raw9493 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9493step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical9493 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9493 = injectiveMoment H node3422 := by
  calc
    injectiveMoment H raw9493 = injectiveMoment H raw9493step0 := by
      have heq : raw9493step0 = (fun i j => raw9493 (permutation199 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9493 permutation199 permutation21
    _ = injectiveMoment H node3422 := by rfl

def raw9494 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0], ![-2, -2, 2, 2]]

def raw9494step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical9494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9494 = injectiveMoment H node2892 := by
  calc
    injectiveMoment H raw9494 = injectiveMoment H raw9494step0 := by
      have heq : raw9494step0 = (fun i j => raw9494 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9494 permutation331 permutation10
    _ = injectiveMoment H node2892 := by rfl

def raw9495 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 1, 3]]

def raw9495step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9495 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9495 = injectiveMoment H node2885 := by
  calc
    injectiveMoment H raw9495 = injectiveMoment H raw9495step0 := by
      have heq : raw9495step0 = (fun i j => raw9495 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9495 permutation308 permutation9
    _ = injectiveMoment H node2885 := by rfl

def raw9496 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9496step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical9496 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9496 = injectiveMoment H node3421 := by
  calc
    injectiveMoment H raw9496 = injectiveMoment H raw9496step0 := by
      have heq : raw9496step0 = (fun i j => raw9496 (permutation199 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9496 permutation199 permutation21
    _ = injectiveMoment H node3421 := by rfl

def raw9497 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw9497step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical9497 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9497 = injectiveMoment H node3198 := by
  calc
    injectiveMoment H raw9497 = injectiveMoment H raw9497step0 := by
      have heq : raw9497step0 = (fun i j => raw9497 (permutation358 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9497 permutation358 permutation14
    _ = injectiveMoment H node3198 := by rfl

def raw9498 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def raw9498step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical9498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9498 = injectiveMoment H node3204 := by
  calc
    injectiveMoment H raw9498 = injectiveMoment H raw9498step0 := by
      have heq : raw9498step0 = (fun i j => raw9498 (permutation264 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9498 permutation264 permutation11
    _ = injectiveMoment H node3204 := by rfl

def raw9499 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def raw9499step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9499 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9499 = injectiveMoment H node3199 := by
  calc
    injectiveMoment H raw9499 = injectiveMoment H raw9499step0 := by
      have heq : raw9499step0 = (fun i j => raw9499 (permutation358 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9499 permutation358 permutation14
    _ = injectiveMoment H node3199 := by rfl

def raw9500 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![1, -1, 1, -1]]

def raw9500step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical9500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9500 = injectiveMoment H node3031 := by
  calc
    injectiveMoment H raw9500 = injectiveMoment H raw9500step0 := by
      have heq : raw9500step0 = (fun i j => raw9500 (permutation264 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9500 permutation264 permutation11
    _ = injectiveMoment H node3031 := by rfl

def raw9501 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 0, 0]]

def raw9501step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9501 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9501 = injectiveMoment H node3433 := by
  calc
    injectiveMoment H raw9501 = injectiveMoment H raw9501step0 := by
      have heq : raw9501step0 = (fun i j => raw9501 (permutation189 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9501 permutation189 permutation21
    _ = injectiveMoment H node3433 := by rfl

def raw9502 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, 1, 0]]

def raw9502step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9502 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9502 = injectiveMoment H node3199 := by
  calc
    injectiveMoment H raw9502 = injectiveMoment H raw9502step0 := by
      have heq : raw9502step0 = (fun i j => raw9502 (permutation357 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9502 permutation357 permutation14
    _ = injectiveMoment H node3199 := by rfl

def raw9503 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1]]

def raw9503step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9503 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9503 = injectiveMoment H node3433 := by
  calc
    injectiveMoment H raw9503 = injectiveMoment H raw9503step0 := by
      have heq : raw9503step0 = (fun i j => raw9503 (permutation199 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9503 permutation199 permutation21
    _ = injectiveMoment H node3433 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
