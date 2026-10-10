import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def raw8608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![-2, -1, 3]]

def raw8608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![-2, -1, 3]]

def raw8608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8608 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8608 = injectiveMoment H node876 := by
  calc
    injectiveMoment H raw8608 = injectiveMoment H raw8608step0 := by
      have heq : raw8608step0 = -raw8608 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8608).symm
    injectiveMoment H raw8608step0 = injectiveMoment H raw8608step1 := by
      have hz : ∀ j, raw8608step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8608step1 = (fun i j => raw8608step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8608step0 permutation221 hz
    injectiveMoment H raw8608step1 = injectiveMoment H raw8608step2 := by
      have heq : raw8608step2 = (fun i j => raw8608step1 (permutation149 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8608step1 permutation149 permutation5
    _ = injectiveMoment H node876 := by rfl

def raw8609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def raw8609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![-1, -2, 3]]

def raw8609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![-1, -2, 3]]

def raw8609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8609 = injectiveMoment H node562 := by
  calc
    injectiveMoment H raw8609 = injectiveMoment H raw8609step0 := by
      have heq : raw8609step0 = -raw8609 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8609).symm
    injectiveMoment H raw8609step0 = injectiveMoment H raw8609step1 := by
      have hz : ∀ j, raw8609step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8609step1 = (fun i j => raw8609step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8609step0 permutation221 hz
    injectiveMoment H raw8609step1 = injectiveMoment H raw8609step2 := by
      have heq : raw8609step2 = (fun i j => raw8609step1 (permutation143 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8609step1 permutation143 permutation5
    _ = injectiveMoment H node562 := by rfl

def raw8610 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical8610 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8610 = injectiveMoment H node1149 := by
  calc
    injectiveMoment H raw8610 = injectiveMoment H raw8610step0 := by
      have hz : ∀ j, raw8610 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8610step0 = (fun i j => raw8610 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8610 permutation221 hz
    injectiveMoment H raw8610step0 = injectiveMoment H raw8610step1 := by
      have heq : raw8610step1 = (fun i j => raw8610step0 (permutation105 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8610step0 permutation105 permutation3
    _ = injectiveMoment H node1149 := by rfl

def raw8611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8611 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8611 = injectiveMoment H node668 := by
  calc
    injectiveMoment H raw8611 = injectiveMoment H raw8611step0 := by
      have hz : ∀ j, raw8611 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8611step0 = (fun i j => raw8611 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8611 permutation221 hz
    injectiveMoment H raw8611step0 = injectiveMoment H raw8611step1 := by
      have heq : raw8611step1 = (fun i j => raw8611step0 (permutation128 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8611step0 permutation128 permutation4
    _ = injectiveMoment H node668 := by rfl

def raw8612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def raw8612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![3, -2, -1]]

def raw8612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2], ![3, -2, -1]]

def raw8612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8612 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8612 = injectiveMoment H node573 := by
  calc
    injectiveMoment H raw8612 = injectiveMoment H raw8612step0 := by
      have heq : raw8612step0 = -raw8612 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8612).symm
    injectiveMoment H raw8612step0 = injectiveMoment H raw8612step1 := by
      have hz : ∀ j, raw8612step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8612step1 = (fun i j => raw8612step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8612step0 permutation221 hz
    injectiveMoment H raw8612step1 = injectiveMoment H raw8612step2 := by
      have heq : raw8612step2 = (fun i j => raw8612step1 (permutation143 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8612step1 permutation143 permutation6
    _ = injectiveMoment H node573 := by rfl

def raw8613 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1]]

def raw8613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8613 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8613 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw8613 = injectiveMoment H raw8613step0 := by
      have heq : raw8613step0 = (fun i j => raw8613 (permutation116 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8613 permutation116 permutation4
    _ = injectiveMoment H node1294 := by rfl

def raw8614 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0]]

def raw8614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8614 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8614 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw8614 = injectiveMoment H raw8614step0 := by
      have heq : raw8614step0 = (fun i j => raw8614 (permutation116 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8614 permutation116 permutation4
    _ = injectiveMoment H node1151 := by rfl

def raw8615 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![2, 2, -4]]

def raw8615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw8615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical8615 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8615 = injectiveMoment H node1536 := by
  calc
    injectiveMoment H raw8615 = injectiveMoment H raw8615step0 := by
      have heq : raw8615step0 = -raw8615 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8615).symm
    injectiveMoment H raw8615step0 = injectiveMoment H raw8615step1 := by
      have heq : raw8615step1 = (fun i j => raw8615step0 (permutation355 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8615step0 permutation355 permutation3
    _ = injectiveMoment H node1536 := by rfl

def raw8616 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1]]

def raw8616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8616 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8616 = injectiveMoment H node2675 := by
  calc
    injectiveMoment H raw8616 = injectiveMoment H raw8616step0 := by
      have heq : raw8616step0 = (fun i j => raw8616 (permutation355 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8616 permutation355 permutation4
    _ = injectiveMoment H node2675 := by rfl

def raw8617 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-3, 1, 2], ![3, 0, -3]]

def raw8617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical8617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8617 = injectiveMoment H node1287 := by
  calc
    injectiveMoment H raw8617 = injectiveMoment H raw8617step0 := by
      have hz : ∀ j, raw8617 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8617step0 = (fun i j => raw8617 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8617 permutation241 hz
    injectiveMoment H raw8617step0 = injectiveMoment H raw8617step1 := by
      have heq : raw8617step1 = (fun i j => raw8617step0 (permutation38 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8617step0 permutation38 permutation5
    _ = injectiveMoment H node1287 := by rfl

def raw8618 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![2, 1, -3]]

def raw8618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![-2, -1, 3]]

def raw8618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical8618 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8618 = injectiveMoment H node555 := by
  calc
    injectiveMoment H raw8618 = injectiveMoment H raw8618step0 := by
      have heq : raw8618step0 = -raw8618 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8618).symm
    injectiveMoment H raw8618step0 = injectiveMoment H raw8618step1 := by
      have hz : ∀ j, raw8618step0 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8618step1 = (fun i j => raw8618step0 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8618step0 permutation241 hz
    injectiveMoment H raw8618step1 = injectiveMoment H raw8618step2 := by
      have heq : raw8618step2 = (fun i j => raw8618step1 (permutation139 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8618step1 permutation139 permutation3
    _ = injectiveMoment H node555 := by rfl

def raw8619 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![2, 0, -2]]

def raw8619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![-2, 0, 2]]

def raw8619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8619 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8619 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw8619 = injectiveMoment H raw8619step0 := by
      have heq : raw8619step0 = -raw8619 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8619).symm
    injectiveMoment H raw8619step0 = injectiveMoment H raw8619step1 := by
      have hz : ∀ j, raw8619step0 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8619step1 = (fun i j => raw8619step0 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8619step0 permutation241 hz
    injectiveMoment H raw8619step1 = injectiveMoment H raw8619step2 := by
      have heq : raw8619step2 = (fun i j => raw8619step1 (permutation139 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8619step1 permutation139 permutation3
    _ = injectiveMoment H node655 := by rfl

def raw8620 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 2, -3]]

def raw8620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![-1, -2, 3]]

def raw8620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw8620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical8620 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8620 = injectiveMoment H node881 := by
  calc
    injectiveMoment H raw8620 = injectiveMoment H raw8620step0 := by
      have heq : raw8620step0 = -raw8620 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8620).symm
    injectiveMoment H raw8620step0 = injectiveMoment H raw8620step1 := by
      have hz : ∀ j, raw8620step0 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8620step1 = (fun i j => raw8620step0 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8620step0 permutation241 hz
    injectiveMoment H raw8620step1 = injectiveMoment H raw8620step2 := by
      have heq : raw8620step2 = (fun i j => raw8620step1 (permutation139 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8620step1 permutation139 permutation3
    _ = injectiveMoment H node881 := by rfl

def raw8621 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 0, 3], ![3, 0, -3]]

def raw8621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8621 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8621 = injectiveMoment H node2787 := by
  calc
    injectiveMoment H raw8621 = injectiveMoment H raw8621step0 := by
      have heq : raw8621step0 = (fun i j => raw8621 (permutation164 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8621 permutation164 permutation5
    _ = injectiveMoment H node2787 := by rfl

def raw8622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, -1, -2]]

def raw8622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

theorem canonical8622 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8622 = injectiveMoment H node1421 := by
  calc
    injectiveMoment H raw8622 = injectiveMoment H raw8622step0 := by
      have heq : raw8622step0 = (fun i j => raw8622 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8622 permutation258 permutation3
    _ = injectiveMoment H node1421 := by rfl

def raw8623 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, -1, 3], ![2, 1, -3]]

def raw8623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical8623 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8623 = injectiveMoment H node1873 := by
  calc
    injectiveMoment H raw8623 = injectiveMoment H raw8623step0 := by
      have heq : raw8623step0 = (fun i j => raw8623 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8623 permutation258 permutation3
    _ = injectiveMoment H node1873 := by rfl

def raw8624 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 0, -2]]

def raw8624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical8624 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8624 = injectiveMoment H node2125 := by
  calc
    injectiveMoment H raw8624 = injectiveMoment H raw8624step0 := by
      have heq : raw8624step0 = (fun i j => raw8624 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8624 permutation258 permutation3
    _ = injectiveMoment H node2125 := by rfl

def raw8625 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, -1, -1]]

def raw8625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8625 = injectiveMoment H node2304 := by
  calc
    injectiveMoment H raw8625 = injectiveMoment H raw8625step0 := by
      have heq : raw8625step0 = (fun i j => raw8625 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8625 permutation258 permutation3
    _ = injectiveMoment H node2304 := by rfl

def raw8626 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0]]

def raw8626step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1]]

def raw8626step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical8626 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8626 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw8626 = injectiveMoment H raw8626step0 := by
      have hz : ∀ j, raw8626 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8626step0 = (fun i j => raw8626 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8626 permutation128 hz
    injectiveMoment H raw8626step0 = injectiveMoment H raw8626step1 := by
      have hz : ∀ i, raw8626step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8626step1 = (fun i j => raw8626step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8626step0 permutation3 hz
    _ = injectiveMoment H node65 := by rfl

def raw8627 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1]]

def raw8627step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw8627step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8627 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8627 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H raw8627 = injectiveMoment H raw8627step0 := by
      have hz : ∀ i, raw8627 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8627step0 = (fun i j => raw8627 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8627 permutation3 hz
    injectiveMoment H raw8627step0 = injectiveMoment H raw8627step1 := by
      have heq : raw8627step1 = (fun i j => raw8627step0 (permutation165 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8627step0 permutation165 permutation1
    _ = injectiveMoment H node1323 := by rfl

def raw8628 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1]]

def raw8628step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![-1, 1]]

def raw8628step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8628 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8628 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw8628 = injectiveMoment H raw8628step0 := by
      have hz : ∀ i, raw8628 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8628step0 = (fun i j => raw8628 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8628 permutation3 hz
    injectiveMoment H raw8628step0 = injectiveMoment H raw8628step1 := by
      have heq : raw8628step1 = (fun i j => raw8628step0 (permutation116 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8628step0 permutation116 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw8629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2], ![1, 3, -4]]

def raw8629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8629 = injectiveMoment H node2127 := by
  calc
    injectiveMoment H raw8629 = injectiveMoment H raw8629step0 := by
      have heq : raw8629step0 = (fun i j => raw8629 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8629 permutation258 permutation3
    _ = injectiveMoment H node2127 := by rfl

def raw8630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 2, -4]]

def raw8630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem canonical8630 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8630 = injectiveMoment H node1399 := by
  calc
    injectiveMoment H raw8630 = injectiveMoment H raw8630step0 := by
      have heq : raw8630step0 = (fun i j => raw8630 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8630 permutation258 permutation3
    _ = injectiveMoment H node1399 := by rfl

def raw8631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-3, 1, 2], ![2, 1, -3]]

def raw8631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical8631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8631 = injectiveMoment H node1422 := by
  calc
    injectiveMoment H raw8631 = injectiveMoment H raw8631step0 := by
      have heq : raw8631step0 = (fun i j => raw8631 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8631 permutation258 permutation3
    _ = injectiveMoment H node1422 := by rfl

def raw8632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 3, -4]]

def raw8632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8632 = injectiveMoment H node1875 := by
  calc
    injectiveMoment H raw8632 = injectiveMoment H raw8632step0 := by
      have heq : raw8632step0 = (fun i j => raw8632 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8632 permutation258 permutation3
    _ = injectiveMoment H node1875 := by rfl

def raw8633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 2, -3]]

def raw8633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8633 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8633 = injectiveMoment H node2128 := by
  calc
    injectiveMoment H raw8633 = injectiveMoment H raw8633step0 := by
      have heq : raw8633step0 = (fun i j => raw8633 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8633 permutation258 permutation3
    _ = injectiveMoment H node2128 := by rfl

def raw8634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1]]

def raw8634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 2, -1]]

def raw8634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8634 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw8634 = injectiveMoment H raw8634step0 := by
      have hz : ∀ j, raw8634 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8634step0 = (fun i j => raw8634 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8634 permutation258 hz
    injectiveMoment H raw8634step0 = injectiveMoment H raw8634step1 := by
      have heq : raw8634step1 = (fun i j => raw8634step0 (permutation139 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8634step0 permutation139 permutation4
    _ = injectiveMoment H node1151 := by rfl

def raw8635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0]]

def raw8635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8635 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8635 = injectiveMoment H node2137 := by
  calc
    injectiveMoment H raw8635 = injectiveMoment H raw8635step0 := by
      have heq : raw8635step0 = (fun i j => raw8635 (permutation356 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8635 permutation356 permutation4
    _ = injectiveMoment H node2137 := by rfl

def raw8636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 2, 1]]

def raw8636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

theorem canonical8636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8636 = injectiveMoment H node1428 := by
  calc
    injectiveMoment H raw8636 = injectiveMoment H raw8636step0 := by
      have heq : raw8636step0 = (fun i j => raw8636 (permutation355 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8636 permutation355 permutation4
    _ = injectiveMoment H node1428 := by rfl

def raw8637 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 0, 3], ![2, 1, -3]]

def raw8637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3], ![-2, -1, 3]]

def raw8637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8637 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8637 = injectiveMoment H node2461 := by
  calc
    injectiveMoment H raw8637 = injectiveMoment H raw8637step0 := by
      have heq : raw8637step0 = -raw8637 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8637).symm
    injectiveMoment H raw8637step0 = injectiveMoment H raw8637step1 := by
      have heq : raw8637step1 = (fun i j => raw8637step0 (permutation366 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8637step0 permutation366 permutation5
    _ = injectiveMoment H node2461 := by rfl

def raw8638 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 0, -2]]

def raw8638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

theorem canonical8638 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8638 = injectiveMoment H node2793 := by
  calc
    injectiveMoment H raw8638 = injectiveMoment H raw8638step0 := by
      have heq : raw8638step0 = (fun i j => raw8638 (permutation161 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8638 permutation161 permutation5
    _ = injectiveMoment H node2793 := by rfl

def raw8639 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, -1, 3], ![1, 2, -3]]

def raw8639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8639 = injectiveMoment H node1876 := by
  calc
    injectiveMoment H raw8639 = injectiveMoment H raw8639step0 := by
      have heq : raw8639step0 = (fun i j => raw8639 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8639 permutation258 permutation3
    _ = injectiveMoment H node1876 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
