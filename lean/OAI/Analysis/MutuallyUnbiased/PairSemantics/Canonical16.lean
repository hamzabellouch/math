import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw512 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]

def raw512step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, -2, 3], ![-2, 2, 0]]

def raw512step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]

def raw512step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical512 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw512 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw512 = injectiveMoment H raw512step0 := by
      have heq : raw512step0 = -raw512 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw512).symm
    injectiveMoment H raw512step0 = injectiveMoment H raw512step1 := by
      have hz : ∀ j, raw512step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw512step1 = (fun i j => raw512step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw512step0 permutation15 hz
    injectiveMoment H raw512step1 = injectiveMoment H raw512step2 := by
      have heq : raw512step2 = (fun i j => raw512step1 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw512step1 permutation5 permutation5
    _ = injectiveMoment H node37 := by rfl

def raw513 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]

def raw513step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical513 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw513 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw513 = injectiveMoment H raw513step0 := by
      have hz : ∀ j, raw513 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw513step0 = (fun i j => raw513 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw513 permutation80 hz
    injectiveMoment H raw513step0 = injectiveMoment H raw513step1 := by
      have heq : raw513step1 = (fun i j => raw513step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw513step0 permutation21 permutation5
    _ = injectiveMoment H node222 := by rfl

def raw514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

theorem canonical514 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw514 = injectiveMoment H node1410 := by
  rfl

def raw515 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

theorem canonical515 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw515 = injectiveMoment H node341 := by
  rfl

def raw516 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

theorem canonical516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw516 = injectiveMoment H node342 := by
  rfl

def raw517 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw517 = injectiveMoment H node699 := by
  calc
    injectiveMoment H raw517 = injectiveMoment H raw517step0 := by
      have heq : raw517step0 = (fun i j => raw517 (permutation108 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw517 permutation108 permutation5
    _ = injectiveMoment H node699 := by rfl

def raw518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical518 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw518 = injectiveMoment H node2791 := by
  calc
    injectiveMoment H raw518 = injectiveMoment H raw518step0 := by
      have heq : raw518step0 = (fun i j => raw518 (permutation252 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw518 permutation252 permutation6
    _ = injectiveMoment H node2791 := by rfl

def raw519 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical519 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw519 = injectiveMoment H node1139 := by
  calc
    injectiveMoment H raw519 = injectiveMoment H raw519step0 := by
      have heq : raw519step0 = (fun i j => raw519 (permutation145 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw519 permutation145 permutation6
    _ = injectiveMoment H node1139 := by rfl

def raw520 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical520 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw520 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw520 = injectiveMoment H raw520step0 := by
      have heq : raw520step0 = (fun i j => raw520 (permutation145 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw520 permutation145 permutation6
    _ = injectiveMoment H node663 := by rfl

def raw521 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw521 = injectiveMoment H node343 := by
  rfl

def raw522 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def raw522step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw522 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw522 = injectiveMoment H raw522step0 := by
      have heq : raw522step0 = (fun i j => raw522 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw522 permutation27 permutation6
    _ = injectiveMoment H node188 := by rfl

def raw523 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

theorem canonical523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw523 = injectiveMoment H node344 := by
  rfl

def raw524 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw524 = injectiveMoment H node345 := by
  rfl

def raw525 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

theorem canonical525 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw525 = injectiveMoment H node346 := by
  rfl

def raw526 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

theorem canonical526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw526 = injectiveMoment H node347 := by
  rfl

def raw527 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]

theorem canonical527 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw527 = injectiveMoment H node93 := by
  rfl

def raw528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

theorem canonical528 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw528 = injectiveMoment H node348 := by
  rfl

def raw529 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]

theorem canonical529 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw529 = injectiveMoment H node94 := by
  rfl

def raw530 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical530 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw530 = injectiveMoment H node349 := by
  rfl

def raw531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical531 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw531 = injectiveMoment H node697 := by
  calc
    injectiveMoment H raw531 = injectiveMoment H raw531step0 := by
      have heq : raw531step0 = (fun i j => raw531 (permutation82 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw531 permutation82 permutation5
    _ = injectiveMoment H node697 := by rfl

def raw532 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical532 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw532 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw532 = injectiveMoment H raw532step0 := by
      have heq : raw532step0 = (fun i j => raw532 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw532 permutation21 permutation5
    _ = injectiveMoment H node222 := by rfl

def raw533 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]

def raw533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical533 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw533 = injectiveMoment H node349 := by
  calc
    injectiveMoment H raw533 = injectiveMoment H raw533step0 := by
      have heq : raw533step0 = (fun i j => raw533 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw533 permutation35 permutation3
    _ = injectiveMoment H node349 := by rfl

def raw534 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical534 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw534 = injectiveMoment H node1139 := by
  calc
    injectiveMoment H raw534 = injectiveMoment H raw534step0 := by
      have heq : raw534step0 = -raw534 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw534).symm
    injectiveMoment H raw534step0 = injectiveMoment H raw534step1 := by
      have heq : raw534step1 = (fun i j => raw534step0 (permutation133 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw534step0 permutation133 permutation5
    _ = injectiveMoment H node1139 := by rfl

def raw535 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical535 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw535 = injectiveMoment H node1293 := by
  calc
    injectiveMoment H raw535 = injectiveMoment H raw535step0 := by
      have heq : raw535step0 = (fun i j => raw535 (permutation96 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw535 permutation96 permutation6
    _ = injectiveMoment H node1293 := by rfl

def raw536 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw536step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical536 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw536 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw536 = injectiveMoment H raw536step0 := by
      have heq : raw536step0 = (fun i j => raw536 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw536 permutation25 permutation6
    _ = injectiveMoment H node292 := by rfl

def raw537 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw537 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw537 = injectiveMoment H raw537step0 := by
      have heq : raw537step0 = (fun i j => raw537 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw537 permutation31 permutation6
    _ = injectiveMoment H node285 := by rfl

def raw538 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw538step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical538 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw538 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw538 = injectiveMoment H raw538step0 := by
      have heq : raw538step0 = (fun i j => raw538 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw538 permutation28 permutation6
    _ = injectiveMoment H node215 := by rfl

def raw539 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]

theorem canonical539 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw539 = injectiveMoment H node95 := by
  rfl

def raw540 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

theorem canonical540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw540 = injectiveMoment H node344 := by
  calc
    injectiveMoment H raw540 = injectiveMoment H raw540step0 := by
      have heq : raw540step0 = (fun i j => raw540 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw540 permutation39 permutation3
    _ = injectiveMoment H node344 := by rfl

def raw541 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw541 = injectiveMoment H node345 := by
  calc
    injectiveMoment H raw541 = injectiveMoment H raw541step0 := by
      have heq : raw541step0 = (fun i j => raw541 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw541 permutation39 permutation3
    _ = injectiveMoment H node345 := by rfl

def raw542 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

theorem canonical542 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw542 = injectiveMoment H node346 := by
  calc
    injectiveMoment H raw542 = injectiveMoment H raw542step0 := by
      have heq : raw542step0 = (fun i j => raw542 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw542 permutation39 permutation3
    _ = injectiveMoment H node346 := by rfl

def raw543 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

theorem canonical543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw543 = injectiveMoment H node347 := by
  calc
    injectiveMoment H raw543 = injectiveMoment H raw543step0 := by
      have heq : raw543step0 = (fun i j => raw543 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw543 permutation39 permutation3
    _ = injectiveMoment H node347 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
