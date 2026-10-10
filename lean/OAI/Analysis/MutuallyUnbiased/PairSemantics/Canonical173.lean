import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5536 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5536 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5536 = injectiveMoment H node255 := by
  rfl

def raw5537 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, -1, 0], ![0, 3, -3]]

def raw5537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5537 = injectiveMoment H node255 := by
  calc
    injectiveMoment H raw5537 = injectiveMoment H raw5537step0 := by
      have heq : raw5537step0 = (fun i j => raw5537 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5537 permutation10 permutation3
    _ = injectiveMoment H node255 := by rfl

def raw5538 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 0, -1], ![0, 2, -2]]

def raw5538step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5538 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5538 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw5538 = injectiveMoment H raw5538step0 := by
      have heq : raw5538step0 = (fun i j => raw5538 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5538 permutation10 permutation3
    _ = injectiveMoment H node254 := by rfl

def raw5539 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1]]

def raw5539step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5539 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5539 = injectiveMoment H node253 := by
  calc
    injectiveMoment H raw5539 = injectiveMoment H raw5539step0 := by
      have heq : raw5539step0 = (fun i j => raw5539 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5539 permutation10 permutation3
    _ = injectiveMoment H node253 := by rfl

def raw5540 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5540 = injectiveMoment H node51 := by
  rfl

def raw5541 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2]]

def raw5541step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5541 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw5541 = injectiveMoment H raw5541step0 := by
      have hz : ∀ j, raw5541 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5541step0 = (fun i j => raw5541 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5541 permutation21 hz
    _ = injectiveMoment H node52 := by rfl

def raw5542 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw5542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5542 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5542 = injectiveMoment H node749 := by
  calc
    injectiveMoment H raw5542 = injectiveMoment H raw5542step0 := by
      have heq : raw5542step0 = (fun i j => raw5542 (permutation41 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5542 permutation41 permutation3
    _ = injectiveMoment H node749 := by rfl

def raw5543 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1]]

def raw5543step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5543 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw5543 = injectiveMoment H raw5543step0 := by
      have heq : raw5543step0 = (fun i j => raw5543 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5543 permutation11 permutation3
    _ = injectiveMoment H node254 := by rfl

def raw5544 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5544 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5544 = injectiveMoment H node256 := by
  rfl

def raw5545 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, -1, 0], ![0, 2, -2]]

def raw5545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5545 = injectiveMoment H node256 := by
  calc
    injectiveMoment H raw5545 = injectiveMoment H raw5545step0 := by
      have heq : raw5545step0 = (fun i j => raw5545 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5545 permutation10 permutation3
    _ = injectiveMoment H node256 := by rfl

def raw5546 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 0, -1], ![0, 1, -1]]

def raw5546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5546 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5546 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw5546 = injectiveMoment H raw5546step0 := by
      have heq : raw5546step0 = (fun i j => raw5546 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5546 permutation13 permutation3
    _ = injectiveMoment H node254 := by rfl

def raw5547 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5547 = injectiveMoment H node52 := by
  rfl

def raw5548 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1]]

def raw5548step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5548 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5548 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw5548 = injectiveMoment H raw5548step0 := by
      have hz : ∀ j, raw5548 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5548step0 = (fun i j => raw5548 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5548 permutation21 hz
    _ = injectiveMoment H node53 := by rfl

def raw5549 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, -1, 0], ![0, 1, -1]]

def raw5549step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5549 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5549 = injectiveMoment H node255 := by
  calc
    injectiveMoment H raw5549 = injectiveMoment H raw5549step0 := by
      have heq : raw5549step0 = (fun i j => raw5549 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5549 permutation13 permutation3
    _ = injectiveMoment H node255 := by rfl

def raw5550 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5550 = injectiveMoment H node53 := by
  rfl

def raw5551 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1], ![0, 0, 0]]

def raw5551step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5551 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5551 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw5551 = injectiveMoment H raw5551step0 := by
      have hz : ∀ j, raw5551 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5551step0 = (fun i j => raw5551 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5551 permutation27 hz
    _ = injectiveMoment H node53 := by rfl

def raw5552 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

theorem canonical5552 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5552 = injectiveMoment H node54 := by
  rfl

def raw5553 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![1, -1, 0], ![0, 4, -4]]

def raw5553step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

theorem canonical5553 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5553 = injectiveMoment H node54 := by
  calc
    injectiveMoment H raw5553 = injectiveMoment H raw5553step0 := by
      have heq : raw5553step0 = (fun i j => raw5553 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5553 permutation4 permutation3
    _ = injectiveMoment H node54 := by rfl

def raw5554 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 0, -1], ![0, 3, -3]]

def raw5554step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5554 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw5554 = injectiveMoment H raw5554step0 := by
      have heq : raw5554step0 = (fun i j => raw5554 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5554 permutation4 permutation3
    _ = injectiveMoment H node53 := by rfl

def raw5555 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![0, 2, -2]]

def raw5555step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5555 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw5555 = injectiveMoment H raw5555step0 := by
      have heq : raw5555step0 = (fun i j => raw5555 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5555 permutation4 permutation3
    _ = injectiveMoment H node52 := by rfl

def raw5556 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 3, -4]]

def raw5556step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![4, -4]]

def raw5556step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical5556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5556 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw5556 = injectiveMoment H raw5556step0 := by
      have heq : raw5556step0 = raw5556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5556).symm
    injectiveMoment H raw5556step0 = injectiveMoment H raw5556step1 := by
      have heq : raw5556step1 = (fun i j => raw5556step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5556step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

def raw5557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical5557 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5557 = injectiveMoment H node2386 := by
  rfl

def raw5558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![-2, 1, 1, 0], ![5, -1, -1, -3]]

def raw5558step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical5558 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5558 = injectiveMoment H node888 := by
  calc
    injectiveMoment H raw5558 = injectiveMoment H raw5558step0 := by
      have heq : raw5558step0 = raw5558.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5558).symm
    injectiveMoment H raw5558step0 = injectiveMoment H raw5558step1 := by
      have heq : raw5558step1 = (fun i j => raw5558step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5558step0 permutation27 permutation18
    _ = injectiveMoment H node888 := by rfl

def raw5559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5559step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem canonical5559 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5559 = injectiveMoment H node2385 := by
  calc
    injectiveMoment H raw5559 = injectiveMoment H raw5559step0 := by
      have heq : raw5559step0 = (fun i j => raw5559 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5559 permutation41 permutation11
    _ = injectiveMoment H node2385 := by rfl

def raw5560 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5560 = injectiveMoment H node2387 := by
  rfl

def raw5561 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw5561step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-2, 1, 0, 1], ![5, -1, -1, -3]]

def raw5561step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical5561 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5561 = injectiveMoment H node889 := by
  calc
    injectiveMoment H raw5561 = injectiveMoment H raw5561step0 := by
      have heq : raw5561step0 = raw5561.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5561).symm
    injectiveMoment H raw5561step0 = injectiveMoment H raw5561step1 := by
      have heq : raw5561step1 = (fun i j => raw5561step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5561step0 permutation27 permutation18
    _ = injectiveMoment H node889 := by rfl

def raw5562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5562 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5562 = injectiveMoment H node2387 := by
  calc
    injectiveMoment H raw5562 = injectiveMoment H raw5562step0 := by
      have heq : raw5562step0 = (fun i j => raw5562 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5562 permutation35 permutation9
    _ = injectiveMoment H node2387 := by rfl

def raw5563 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical5563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5563 = injectiveMoment H node750 := by
  rfl

def raw5564 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical5564 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5564 = injectiveMoment H node751 := by
  rfl

def raw5565 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw5565step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![5, -1, -3, -1]]

def raw5565step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5565 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5565 = injectiveMoment H node890 := by
  calc
    injectiveMoment H raw5565 = injectiveMoment H raw5565step0 := by
      have heq : raw5565step0 = raw5565.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5565).symm
    injectiveMoment H raw5565step0 = injectiveMoment H raw5565step1 := by
      have heq : raw5565step1 = (fun i j => raw5565step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5565step0 permutation29 permutation20
    _ = injectiveMoment H node890 := by rfl

def raw5566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical5566 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5566 = injectiveMoment H node2386 := by
  calc
    injectiveMoment H raw5566 = injectiveMoment H raw5566step0 := by
      have heq : raw5566step0 = (fun i j => raw5566 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5566 permutation41 permutation11
    _ = injectiveMoment H node2386 := by rfl

def raw5567 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw5567step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical5567 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5567 = injectiveMoment H node751 := by
  calc
    injectiveMoment H raw5567 = injectiveMoment H raw5567step0 := by
      have heq : raw5567step0 = (fun i j => raw5567 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5567 permutation11 permutation11
    _ = injectiveMoment H node751 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
