import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9408 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9408step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9408step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9408step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical9408 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9408 = injectiveMoment H node1512 := by
  calc
    injectiveMoment H raw9408 = injectiveMoment H raw9408step0 := by
      have heq : raw9408step0 = -raw9408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9408).symm
    injectiveMoment H raw9408step0 = injectiveMoment H raw9408step1 := by
      have hz : ∀ j, raw9408step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9408step1 = (fun i j => raw9408step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9408step0 permutation202 hz
    injectiveMoment H raw9408step1 = injectiveMoment H raw9408step2 := by
      have heq : raw9408step2 = (fun i j => raw9408step1 (permutation135 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9408step1 permutation135 permutation23
    _ = injectiveMoment H node1512 := by rfl

def raw9409 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9409step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2], ![0, -2, -1, 3]]

def raw9409step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2], ![0, -2, -1, 3]]

def raw9409step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical9409 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9409 = injectiveMoment H node1718 := by
  calc
    injectiveMoment H raw9409 = injectiveMoment H raw9409step0 := by
      have heq : raw9409step0 = -raw9409 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9409).symm
    injectiveMoment H raw9409step0 = injectiveMoment H raw9409step1 := by
      have hz : ∀ j, raw9409step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9409step1 = (fun i j => raw9409step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9409step0 permutation202 hz
    injectiveMoment H raw9409step1 = injectiveMoment H raw9409step2 := by
      have heq : raw9409step2 = (fun i j => raw9409step1 (permutation140 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9409step1 permutation140 permutation17
    _ = injectiveMoment H node1718 := by rfl

def raw9410 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9410step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9410step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9410step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical9410 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9410 = injectiveMoment H node1513 := by
  calc
    injectiveMoment H raw9410 = injectiveMoment H raw9410step0 := by
      have heq : raw9410step0 = -raw9410 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9410).symm
    injectiveMoment H raw9410step0 = injectiveMoment H raw9410step1 := by
      have hz : ∀ j, raw9410step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9410step1 = (fun i j => raw9410step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9410step0 permutation202 hz
    injectiveMoment H raw9410step1 = injectiveMoment H raw9410step2 := by
      have heq : raw9410step2 = (fun i j => raw9410step1 (permutation139 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9410step1 permutation139 permutation17
    _ = injectiveMoment H node1513 := by rfl

def raw9411 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9411step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9411step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical9411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9411 = injectiveMoment H node1825 := by
  calc
    injectiveMoment H raw9411 = injectiveMoment H raw9411step0 := by
      have hz : ∀ j, raw9411 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9411step0 = (fun i j => raw9411 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9411 permutation202 hz
    injectiveMoment H raw9411step0 = injectiveMoment H raw9411step1 := by
      have heq : raw9411step1 = (fun i j => raw9411step0 (permutation142 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9411step0 permutation142 permutation28
    _ = injectiveMoment H node1825 := by rfl

def raw9412 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9412step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9412step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9412 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9412 = injectiveMoment H node1800 := by
  calc
    injectiveMoment H raw9412 = injectiveMoment H raw9412step0 := by
      have hz : ∀ j, raw9412 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9412step0 = (fun i j => raw9412 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9412 permutation202 hz
    injectiveMoment H raw9412step0 = injectiveMoment H raw9412step1 := by
      have heq : raw9412step1 = (fun i j => raw9412step0 (permutation132 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9412step0 permutation132 permutation10
    _ = injectiveMoment H node1800 := by rfl

def raw9413 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9413step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9413step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9413step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical9413 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9413 = injectiveMoment H node2443 := by
  calc
    injectiveMoment H raw9413 = injectiveMoment H raw9413step0 := by
      have heq : raw9413step0 = -raw9413 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9413).symm
    injectiveMoment H raw9413step0 = injectiveMoment H raw9413step1 := by
      have hz : ∀ j, raw9413step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9413step1 = (fun i j => raw9413step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9413step0 permutation202 hz
    injectiveMoment H raw9413step1 = injectiveMoment H raw9413step2 := by
      have heq : raw9413step2 = (fun i j => raw9413step1 (permutation142 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9413step1 permutation142 permutation23
    _ = injectiveMoment H node2443 := by rfl

def raw9414 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9414step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9414step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9414step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical9414 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9414 = injectiveMoment H node1520 := by
  calc
    injectiveMoment H raw9414 = injectiveMoment H raw9414step0 := by
      have heq : raw9414step0 = -raw9414 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9414).symm
    injectiveMoment H raw9414step0 = injectiveMoment H raw9414step1 := by
      have hz : ∀ j, raw9414step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9414step1 = (fun i j => raw9414step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9414step0 permutation202 hz
    injectiveMoment H raw9414step1 = injectiveMoment H raw9414step2 := by
      have heq : raw9414step2 = (fun i j => raw9414step1 (permutation141 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9414step1 permutation141 permutation23
    _ = injectiveMoment H node1520 := by rfl

def raw9415 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9415step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9415step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical9415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9415 = injectiveMoment H node2769 := by
  calc
    injectiveMoment H raw9415 = injectiveMoment H raw9415step0 := by
      have hz : ∀ j, raw9415 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9415step0 = (fun i j => raw9415 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9415 permutation202 hz
    injectiveMoment H raw9415step0 = injectiveMoment H raw9415step1 := by
      have heq : raw9415step1 = (fun i j => raw9415step0 (permutation33 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9415step0 permutation33 permutation23
    _ = injectiveMoment H node2769 := by rfl

def raw9416 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9416step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9416 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9416 = injectiveMoment H node2756 := by
  calc
    injectiveMoment H raw9416 = injectiveMoment H raw9416step0 := by
      have heq : raw9416step0 = (fun i j => raw9416 (permutation65 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9416 permutation65 permutation27
    _ = injectiveMoment H node2756 := by rfl

def raw9417 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, -1, 1, -1]]

def raw9417step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

theorem canonical9417 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9417 = injectiveMoment H node1349 := by
  calc
    injectiveMoment H raw9417 = injectiveMoment H raw9417step0 := by
      have heq : raw9417step0 = (fun i j => raw9417 (permutation21 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9417 permutation21 permutation9
    _ = injectiveMoment H node1349 := by rfl

def raw9418 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -2, -1, 2]]

def raw9418step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 1, 1, -1], ![1, -1, -2, 2]]

def raw9418step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem canonical9418 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9418 = injectiveMoment H node1335 := by
  calc
    injectiveMoment H raw9418 = injectiveMoment H raw9418step0 := by
      have heq : raw9418step0 = raw9418.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9418).symm
    injectiveMoment H raw9418step0 = injectiveMoment H raw9418step1 := by
      have heq : raw9418step1 = (fun i j => raw9418step0 (permutation27 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9418step0 permutation27 permutation15
    _ = injectiveMoment H node1335 := by rfl

def raw9419 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 2, 2, -3], ![1, -2, -2, 3]]

def raw9419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 1, 2, -2], ![1, -1, -3, 3]]

def raw9419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 2, -2]]

theorem canonical9419 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9419 = injectiveMoment H node1328 := by
  calc
    injectiveMoment H raw9419 = injectiveMoment H raw9419step0 := by
      have heq : raw9419step0 = raw9419.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9419).symm
    injectiveMoment H raw9419step0 = injectiveMoment H raw9419step1 := by
      have heq : raw9419step1 = (fun i j => raw9419step0 (permutation27 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9419step0 permutation27 permutation15
    _ = injectiveMoment H node1328 := by rfl

def raw9420 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw9420step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem canonical9420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9420 = injectiveMoment H node2959 := by
  calc
    injectiveMoment H raw9420 = injectiveMoment H raw9420step0 := by
      have heq : raw9420step0 = (fun i j => raw9420 (permutation283 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9420 permutation283 permutation9
    _ = injectiveMoment H node2959 := by rfl

def raw9421 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def raw9421step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9421 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9421 = injectiveMoment H node3436 := by
  calc
    injectiveMoment H raw9421 = injectiveMoment H raw9421step0 := by
      have heq : raw9421step0 = (fun i j => raw9421 (permutation219 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9421 permutation219 permutation27
    _ = injectiveMoment H node3436 := by rfl

def raw9422 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw9422step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -1, 0]]

def raw9422step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9422 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9422 = injectiveMoment H node3393 := by
  calc
    injectiveMoment H raw9422 = injectiveMoment H raw9422step0 := by
      have heq : raw9422step0 = -raw9422 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9422).symm
    injectiveMoment H raw9422step0 = injectiveMoment H raw9422step1 := by
      have heq : raw9422step1 = (fun i j => raw9422step0 (permutation349 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9422step0 permutation349 permutation18
    _ = injectiveMoment H node3393 := by rfl

def raw9423 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9423step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9423step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical9423 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9423 = injectiveMoment H node2743 := by
  calc
    injectiveMoment H raw9423 = injectiveMoment H raw9423step0 := by
      have hz : ∀ j, raw9423 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9423step0 = (fun i j => raw9423 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9423 permutation221 hz
    injectiveMoment H raw9423step0 = injectiveMoment H raw9423step1 := by
      have heq : raw9423step1 = (fun i j => raw9423step0 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9423step0 permutation48 permutation21
    _ = injectiveMoment H node2743 := by rfl

def raw9424 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def raw9424step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9424step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9424step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9424 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9424 = injectiveMoment H node1747 := by
  calc
    injectiveMoment H raw9424 = injectiveMoment H raw9424step0 := by
      have heq : raw9424step0 = -raw9424 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9424).symm
    injectiveMoment H raw9424step0 = injectiveMoment H raw9424step1 := by
      have hz : ∀ j, raw9424step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9424step1 = (fun i j => raw9424step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9424step0 permutation221 hz
    injectiveMoment H raw9424step1 = injectiveMoment H raw9424step2 := by
      have heq : raw9424step2 = (fun i j => raw9424step1 (permutation128 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9424step1 permutation128 permutation14
    _ = injectiveMoment H node1747 := by rfl

def raw9425 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9425step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9425step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical9425 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9425 = injectiveMoment H node2738 := by
  calc
    injectiveMoment H raw9425 = injectiveMoment H raw9425step0 := by
      have hz : ∀ j, raw9425 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9425step0 = (fun i j => raw9425 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9425 permutation221 hz
    injectiveMoment H raw9425step0 = injectiveMoment H raw9425step1 := by
      have heq : raw9425step1 = (fun i j => raw9425step0 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9425step0 permutation48 permutation21
    _ = injectiveMoment H node2738 := by rfl

def raw9426 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9426step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9426step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

theorem canonical9426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9426 = injectiveMoment H node2851 := by
  calc
    injectiveMoment H raw9426 = injectiveMoment H raw9426step0 := by
      have hz : ∀ j, raw9426 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9426step0 = (fun i j => raw9426 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9426 permutation221 hz
    injectiveMoment H raw9426step0 = injectiveMoment H raw9426step1 := by
      have heq : raw9426step1 = (fun i j => raw9426step0 (permutation54 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9426step0 permutation54 permutation25
    _ = injectiveMoment H node2851 := by rfl

def raw9427 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw9427step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, -1, -1, 0]]

def raw9427step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, -1, -1, 0]]

def raw9427step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9427 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9427 = injectiveMoment H node2724 := by
  calc
    injectiveMoment H raw9427 = injectiveMoment H raw9427step0 := by
      have heq : raw9427step0 = -raw9427 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9427).symm
    injectiveMoment H raw9427step0 = injectiveMoment H raw9427step1 := by
      have hz : ∀ j, raw9427step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9427step1 = (fun i j => raw9427step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9427step0 permutation221 hz
    injectiveMoment H raw9427step1 = injectiveMoment H raw9427step2 := by
      have heq : raw9427step2 = (fun i j => raw9427step1 (permutation132 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9427step1 permutation132 permutation20
    _ = injectiveMoment H node2724 := by rfl

def raw9428 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, -1, 0, 0]]

def raw9428step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

theorem canonical9428 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9428 = injectiveMoment H node2846 := by
  calc
    injectiveMoment H raw9428 = injectiveMoment H raw9428step0 := by
      have heq : raw9428step0 = (fun i j => raw9428 (permutation104 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9428 permutation104 permutation9
    _ = injectiveMoment H node2846 := by rfl

def raw9429 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw9429step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

theorem canonical9429 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9429 = injectiveMoment H node3335 := by
  calc
    injectiveMoment H raw9429 = injectiveMoment H raw9429step0 := by
      have heq : raw9429step0 = (fun i j => raw9429 (permutation270 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9429 permutation270 permutation15
    _ = injectiveMoment H node3335 := by rfl

def raw9430 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -2, 0, 4], ![2, 1, 0, -3]]

def raw9430step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem canonical9430 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9430 = injectiveMoment H node2869 := by
  calc
    injectiveMoment H raw9430 = injectiveMoment H raw9430step0 := by
      have heq : raw9430step0 = (fun i j => raw9430 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9430 permutation258 permutation9
    _ = injectiveMoment H node2869 := by rfl

def raw9431 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 0, 0, -2]]

def raw9431step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical9431 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9431 = injectiveMoment H node3336 := by
  calc
    injectiveMoment H raw9431 = injectiveMoment H raw9431step0 := by
      have heq : raw9431step0 = (fun i j => raw9431 (permutation259 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9431 permutation259 permutation15
    _ = injectiveMoment H node3336 := by rfl

def raw9432 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9432step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 2, 0, 0]]

def raw9432step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9432 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9432 = injectiveMoment H node3166 := by
  calc
    injectiveMoment H raw9432 = injectiveMoment H raw9432step0 := by
      have heq : raw9432step0 = -raw9432 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9432).symm
    injectiveMoment H raw9432step0 = injectiveMoment H raw9432step1 := by
      have heq : raw9432step1 = (fun i j => raw9432step0 (permutation337 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9432step0 permutation337 permutation12
    _ = injectiveMoment H node3166 := by rfl

def raw9433 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def raw9433step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9433step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9433 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9433 = injectiveMoment H node3092 := by
  calc
    injectiveMoment H raw9433 = injectiveMoment H raw9433step0 := by
      have heq : raw9433step0 = -raw9433 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9433).symm
    injectiveMoment H raw9433step0 = injectiveMoment H raw9433step1 := by
      have heq : raw9433step1 = (fun i j => raw9433step0 (permutation320 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9433step0 permutation320 permutation13
    _ = injectiveMoment H node3092 := by rfl

def raw9434 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 0, 1]]

def raw9434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1]]

def raw9434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical9434 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9434 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw9434 = injectiveMoment H raw9434step0 := by
      have hz : ∀ i, raw9434 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9434step0 = (fun i j => raw9434 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9434 permutation9 hz
    injectiveMoment H raw9434step0 = injectiveMoment H raw9434step1 := by
      have heq : raw9434step1 = (fun i j => raw9434step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9434step0 permutation128 permutation3
    _ = injectiveMoment H node1294 := by rfl

def raw9435 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, -1, 2], ![2, -2, 0, 0]]

def raw9435step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9435 = injectiveMoment H node3030 := by
  calc
    injectiveMoment H raw9435 = injectiveMoment H raw9435step0 := by
      have heq : raw9435step0 = (fun i j => raw9435 (permutation270 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9435 permutation270 permutation11
    _ = injectiveMoment H node3030 := by rfl

def raw9436 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -1, 1]]

def raw9436step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem canonical9436 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9436 = injectiveMoment H node3097 := by
  calc
    injectiveMoment H raw9436 = injectiveMoment H raw9436step0 := by
      have heq : raw9436step0 = (fun i j => raw9436 (permutation309 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9436 permutation309 permutation17
    _ = injectiveMoment H node3097 := by rfl

def raw9437 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -2, 2]]

def raw9437step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical9437 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9437 = injectiveMoment H node3288 := by
  calc
    injectiveMoment H raw9437 = injectiveMoment H raw9437step0 := by
      have heq : raw9437step0 = (fun i j => raw9437 (permutation280 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9437 permutation280 permutation10
    _ = injectiveMoment H node3288 := by rfl

def raw9438 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def raw9438step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![-1, 0, 1, 0], ![2, -2, 0, 0]]

def raw9438step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9438 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9438 = injectiveMoment H node3166 := by
  calc
    injectiveMoment H raw9438 = injectiveMoment H raw9438step0 := by
      have heq : raw9438step0 = -raw9438 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9438).symm
    injectiveMoment H raw9438step0 = injectiveMoment H raw9438step1 := by
      have heq : raw9438step1 = (fun i j => raw9438step0 (permutation338 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9438step0 permutation338 permutation18
    _ = injectiveMoment H node3166 := by rfl

def raw9439 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9439step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![2, 1, 0, -3], ![-1, -2, 0, 3]]

def raw9439step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

theorem canonical9439 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9439 = injectiveMoment H node2983 := by
  calc
    injectiveMoment H raw9439 = injectiveMoment H raw9439step0 := by
      have heq : raw9439step0 = -raw9439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9439).symm
    injectiveMoment H raw9439step0 = injectiveMoment H raw9439step1 := by
      have heq : raw9439step1 = (fun i j => raw9439step0 (permutation337 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9439step0 permutation337 permutation15
    _ = injectiveMoment H node2983 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
