import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8512 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, -1, 3, -3]]

def raw8512step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical8512 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8512 = injectiveMoment H node3163 := by
  calc
    injectiveMoment H raw8512 = injectiveMoment H raw8512step0 := by
      have heq : raw8512step0 = (fun i j => raw8512 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8512 permutation259 permutation9
    _ = injectiveMoment H node3163 := by rfl

def raw8513 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, -1, -1, 2]]

def raw8513step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2]]

def raw8513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![1, 1, -2]]

def raw8513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8513 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8513 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw8513 = injectiveMoment H raw8513step0 := by
      have heq : raw8513step0 = -raw8513 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8513).symm
    injectiveMoment H raw8513step0 = injectiveMoment H raw8513step1 := by
      have hz : ∀ i, raw8513step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8513step1 = (fun i j => raw8513step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8513step0 permutation9 hz
    injectiveMoment H raw8513step1 = injectiveMoment H raw8513step2 := by
      have heq : raw8513step2 = (fun i j => raw8513step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8513step1 permutation21 permutation5
    _ = injectiveMoment H node181 := by rfl

def raw8514 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8514step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical8514 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8514 = injectiveMoment H node3164 := by
  calc
    injectiveMoment H raw8514 = injectiveMoment H raw8514step0 := by
      have heq : raw8514step0 = (fun i j => raw8514 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8514 permutation262 permutation9
    _ = injectiveMoment H node3164 := by rfl

def raw8515 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8515step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical8515 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8515 = injectiveMoment H node3164 := by
  calc
    injectiveMoment H raw8515 = injectiveMoment H raw8515step0 := by
      have heq : raw8515step0 = (fun i j => raw8515 (permutation263 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8515 permutation263 permutation9
    _ = injectiveMoment H node3164 := by rfl

def raw8516 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4]]

def raw8516step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical8516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8516 = injectiveMoment H node2956 := by
  calc
    injectiveMoment H raw8516 = injectiveMoment H raw8516step0 := by
      have heq : raw8516step0 = (fun i j => raw8516 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8516 permutation262 permutation9
    _ = injectiveMoment H node2956 := by rfl

def raw8517 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 0, 3, -3]]

def raw8517step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical8517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8517 = injectiveMoment H node3427 := by
  calc
    injectiveMoment H raw8517 = injectiveMoment H raw8517step0 := by
      have heq : raw8517step0 = (fun i j => raw8517 (permutation196 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8517 permutation196 permutation15
    _ = injectiveMoment H node3427 := by rfl

def raw8518 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, -1, -2, 2]]

def raw8518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, -2, 2]]

def raw8518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem canonical8518 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8518 = injectiveMoment H node1335 := by
  calc
    injectiveMoment H raw8518 = injectiveMoment H raw8518step0 := by
      have heq : raw8518step0 = raw8518.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8518).symm
    injectiveMoment H raw8518step0 = injectiveMoment H raw8518step1 := by
      have heq : raw8518step1 = (fun i j => raw8518step0 (permutation28 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8518step0 permutation28 permutation15
    _ = injectiveMoment H node1335 := by rfl

def raw8519 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -1, -1, 2]]

def raw8519step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw8519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical8519 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8519 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw8519 = injectiveMoment H raw8519step0 := by
      have hz : ∀ i, raw8519 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8519step0 = (fun i j => raw8519 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8519 permutation9 hz
    injectiveMoment H raw8519step0 = injectiveMoment H raw8519step1 := by
      have heq : raw8519step1 = (fun i j => raw8519step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8519step0 permutation27 permutation5
    _ = injectiveMoment H node283 := by rfl

def raw8520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def raw8520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![-2, -1, 3]]

def raw8520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

theorem canonical8520 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8520 = injectiveMoment H node1889 := by
  calc
    injectiveMoment H raw8520 = injectiveMoment H raw8520step0 := by
      have heq : raw8520step0 = -raw8520 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8520).symm
    injectiveMoment H raw8520step0 = injectiveMoment H raw8520step1 := by
      have heq : raw8520step1 = (fun i j => raw8520step0 (permutation317 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8520step0 permutation317 permutation3
    _ = injectiveMoment H node1889 := by rfl

def raw8521 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw8521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical8521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8521 = injectiveMoment H node1150 := by
  calc
    injectiveMoment H raw8521 = injectiveMoment H raw8521step0 := by
      have heq : raw8521step0 = (fun i j => raw8521 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8521 permutation57 permutation3
    _ = injectiveMoment H node1150 := by rfl

def raw8522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def raw8522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]

def raw8522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical8522 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8522 = injectiveMoment H node1862 := by
  calc
    injectiveMoment H raw8522 = injectiveMoment H raw8522step0 := by
      have heq : raw8522step0 = -raw8522 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8522).symm
    injectiveMoment H raw8522step0 = injectiveMoment H raw8522step1 := by
      have heq : raw8522step1 = (fun i j => raw8522step0 (permutation375 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8522step0 permutation375 permutation3
    _ = injectiveMoment H node1862 := by rfl

def raw8523 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def raw8523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8523 = injectiveMoment H node2382 := by
  calc
    injectiveMoment H raw8523 = injectiveMoment H raw8523step0 := by
      have heq : raw8523step0 = (fun i j => raw8523 (permutation332 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8523 permutation332 permutation4
    _ = injectiveMoment H node2382 := by rfl

def raw8524 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def raw8524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8524 = injectiveMoment H node2671 := by
  calc
    injectiveMoment H raw8524 = injectiveMoment H raw8524step0 := by
      have heq : raw8524step0 = (fun i j => raw8524 (permutation215 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8524 permutation215 permutation3
    _ = injectiveMoment H node2671 := by rfl

def raw8525 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def raw8525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical8525 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8525 = injectiveMoment H node1532 := by
  calc
    injectiveMoment H raw8525 = injectiveMoment H raw8525step0 := by
      have heq : raw8525step0 = (fun i j => raw8525 (permutation331 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8525 permutation331 permutation4
    _ = injectiveMoment H node1532 := by rfl

def raw8526 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8526 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw8526 = injectiveMoment H raw8526step0 := by
      have heq : raw8526step0 = (fun i j => raw8526 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8526 permutation57 permutation3
    _ = injectiveMoment H node1151 := by rfl

def raw8527 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw8527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8527 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8527 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H raw8527 = injectiveMoment H raw8527step0 := by
      have heq : raw8527step0 = (fun i j => raw8527 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8527 permutation57 permutation3
    _ = injectiveMoment H node1152 := by rfl

def raw8528 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def raw8528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![-2, -2, 4]]

def raw8528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8528 = injectiveMoment H node1528 := by
  calc
    injectiveMoment H raw8528 = injectiveMoment H raw8528step0 := by
      have heq : raw8528step0 = -raw8528 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8528).symm
    injectiveMoment H raw8528step0 = injectiveMoment H raw8528step1 := by
      have heq : raw8528step1 = (fun i j => raw8528step0 (permutation371 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8528step0 permutation371 permutation5
    _ = injectiveMoment H node1528 := by rfl

def raw8529 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def raw8529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8529 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8529 = injectiveMoment H node2669 := by
  calc
    injectiveMoment H raw8529 = injectiveMoment H raw8529step0 := by
      have heq : raw8529step0 = (fun i j => raw8529 (permutation215 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8529 permutation215 permutation3
    _ = injectiveMoment H node2669 := by rfl

def raw8530 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def raw8530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw8530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical8530 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8530 = injectiveMoment H node2459 := by
  calc
    injectiveMoment H raw8530 = injectiveMoment H raw8530step0 := by
      have heq : raw8530step0 = -raw8530 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8530).symm
    injectiveMoment H raw8530step0 = injectiveMoment H raw8530step1 := by
      have heq : raw8530step1 = (fun i j => raw8530step0 (permutation383 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8530step0 permutation383 permutation3
    _ = injectiveMoment H node2459 := by rfl

def raw8531 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0]]

def raw8531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical8531 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8531 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw8531 = injectiveMoment H raw8531step0 := by
      have heq : raw8531step0 = (fun i j => raw8531 (permutation15 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8531 permutation15 permutation3
    _ = injectiveMoment H node285 := by rfl

def raw8532 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1]]

def raw8532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

theorem canonical8532 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8532 = injectiveMoment H node286 := by
  calc
    injectiveMoment H raw8532 = injectiveMoment H raw8532step0 := by
      have heq : raw8532step0 = (fun i j => raw8532 (permutation15 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8532 permutation15 permutation3
    _ = injectiveMoment H node286 := by rfl

def raw8533 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def raw8533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8533 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8533 = injectiveMoment H node2294 := by
  calc
    injectiveMoment H raw8533 = injectiveMoment H raw8533step0 := by
      have heq : raw8533step0 = (fun i j => raw8533 (permutation277 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8533 permutation277 permutation3
    _ = injectiveMoment H node2294 := by rfl

def raw8534 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def raw8534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8534 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8534 = injectiveMoment H node2650 := by
  calc
    injectiveMoment H raw8534 = injectiveMoment H raw8534step0 := by
      have heq : raw8534step0 = (fun i j => raw8534 (permutation214 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8534 permutation214 permutation3
    _ = injectiveMoment H node2650 := by rfl

def raw8535 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1]]

def raw8535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8535 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8535 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw8535 = injectiveMoment H raw8535step0 := by
      have heq : raw8535step0 = (fun i j => raw8535 (permutation60 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8535 permutation60 permutation3
    _ = injectiveMoment H node1151 := by rfl

def raw8536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8536 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8536 = injectiveMoment H node2649 := by
  calc
    injectiveMoment H raw8536 = injectiveMoment H raw8536step0 := by
      have heq : raw8536step0 = (fun i j => raw8536 (permutation214 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8536 permutation214 permutation3
    _ = injectiveMoment H node2649 := by rfl

def raw8537 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0]]

def raw8537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8537 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw8537 = injectiveMoment H raw8537step0 := by
      have heq : raw8537step0 = (fun i j => raw8537 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8537 permutation17 permutation4
    _ = injectiveMoment H node293 := by rfl

def raw8538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def raw8538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical8538 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8538 = injectiveMoment H node1858 := by
  calc
    injectiveMoment H raw8538 = injectiveMoment H raw8538step0 := by
      have heq : raw8538step0 = (fun i j => raw8538 (permutation277 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8538 permutation277 permutation3
    _ = injectiveMoment H node1858 := by rfl

def raw8539 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw8539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8539 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8539 = injectiveMoment H node2465 := by
  calc
    injectiveMoment H raw8539 = injectiveMoment H raw8539step0 := by
      have heq : raw8539step0 = (fun i j => raw8539 (permutation277 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8539 permutation277 permutation3
    _ = injectiveMoment H node2465 := by rfl

def raw8540 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8540 = injectiveMoment H node2660 := by
  calc
    injectiveMoment H raw8540 = injectiveMoment H raw8540step0 := by
      have heq : raw8540step0 = (fun i j => raw8540 (permutation324 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8540 permutation324 permutation5
    _ = injectiveMoment H node2660 := by rfl

def raw8541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def raw8541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8541 = injectiveMoment H node2468 := by
  calc
    injectiveMoment H raw8541 = injectiveMoment H raw8541step0 := by
      have heq : raw8541step0 = (fun i j => raw8541 (permutation279 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8541 permutation279 permutation3
    _ = injectiveMoment H node2468 := by rfl

def raw8542 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1]]

def raw8542step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8542 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8542 = injectiveMoment H node64 := by
  calc
    injectiveMoment H raw8542 = injectiveMoment H raw8542step0 := by
      have heq : raw8542step0 = (fun i j => raw8542 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8542 permutation5 permutation4
    _ = injectiveMoment H node64 := by rfl

def raw8543 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8543 = injectiveMoment H node1854 := by
  calc
    injectiveMoment H raw8543 = injectiveMoment H raw8543step0 := by
      have heq : raw8543step0 = (fun i j => raw8543 (permutation277 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8543 permutation277 permutation4
    _ = injectiveMoment H node1854 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
