import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6464 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![0, 1, -2, 1]]

def raw6464step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6464 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6464 = injectiveMoment H node2602 := by
  calc
    injectiveMoment H raw6464 = injectiveMoment H raw6464step0 := by
      have heq : raw6464step0 = (fun i j => raw6464 (permutation37 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6464 permutation37 permutation9
    _ = injectiveMoment H node2602 := by rfl

def raw6465 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6465 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6465 = injectiveMoment H node1044 := by
  rfl

def raw6466 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6466step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6466 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw6466 = injectiveMoment H raw6466step0 := by
      have heq : raw6466step0 = (fun i j => raw6466 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6466 permutation10 permutation15
    _ = injectiveMoment H node1044 := by rfl

def raw6467 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6467step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6467 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6467 = injectiveMoment H node1043 := by
  calc
    injectiveMoment H raw6467 = injectiveMoment H raw6467step0 := by
      have heq : raw6467step0 = (fun i j => raw6467 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6467 permutation10 permutation15
    _ = injectiveMoment H node1043 := by rfl

def raw6468 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw6468step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical6468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6468 = injectiveMoment H node1042 := by
  calc
    injectiveMoment H raw6468 = injectiveMoment H raw6468step0 := by
      have heq : raw6468step0 = (fun i j => raw6468 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6468 permutation10 permutation15
    _ = injectiveMoment H node1042 := by rfl

def raw6469 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw6469step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![2, 1, 0, -3]]

def raw6469step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical6469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6469 = injectiveMoment H node799 := by
  calc
    injectiveMoment H raw6469 = injectiveMoment H raw6469step0 := by
      have heq : raw6469step0 = raw6469.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6469).symm
    injectiveMoment H raw6469step0 = injectiveMoment H raw6469step1 := by
      have heq : raw6469step1 = (fun i j => raw6469step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6469step0 permutation21 permutation17
    _ = injectiveMoment H node799 := by rfl

def raw6470 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6470step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 1, -1, 1]]

def raw6470step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6470 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6470 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw6470 = injectiveMoment H raw6470step0 := by
      have heq : raw6470step0 = -raw6470 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6470).symm
    injectiveMoment H raw6470step0 = injectiveMoment H raw6470step1 := by
      have heq : raw6470step1 = (fun i j => raw6470step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6470step0 permutation32 permutation11
    _ = injectiveMoment H node1110 := by rfl

def raw6471 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-1, 1, 0, 0]]

def raw6471step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical6471 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6471 = injectiveMoment H node1203 := by
  calc
    injectiveMoment H raw6471 = injectiveMoment H raw6471step0 := by
      have heq : raw6471step0 = -raw6471 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6471).symm
    injectiveMoment H raw6471step0 = injectiveMoment H raw6471step1 := by
      have heq : raw6471step1 = (fun i j => raw6471step0 (permutation25 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6471step0 permutation25 permutation21
    _ = injectiveMoment H node1203 := by rfl

def raw6472 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw6472step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![2, 1, -4, 1]]

def raw6472step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![-2, -1, 4, -1]]

def raw6472step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical6472 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6472 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw6472 = injectiveMoment H raw6472step0 := by
      have heq : raw6472step0 = raw6472.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6472).symm
    injectiveMoment H raw6472step0 = injectiveMoment H raw6472step1 := by
      have heq : raw6472step1 = -raw6472step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6472step0).symm
    injectiveMoment H raw6472step1 = injectiveMoment H raw6472step2 := by
      have heq : raw6472step2 = (fun i j => raw6472step1 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6472step1 permutation27 permutation16
    _ = injectiveMoment H node786 := by rfl

def raw6473 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6473step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![2, 0, -2, 0]]

def raw6473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0]]

def raw6473step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6473 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6473 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw6473 = injectiveMoment H raw6473step0 := by
      have heq : raw6473step0 = raw6473.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6473).symm
    injectiveMoment H raw6473step0 = injectiveMoment H raw6473step1 := by
      have hz : ∀ i, raw6473step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw6473step1 = (fun i j => raw6473step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6473step0 permutation15 hz
    injectiveMoment H raw6473step1 = injectiveMoment H raw6473step2 := by
      have heq : raw6473step2 = (fun i j => raw6473step1 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6473step1 permutation24 permutation7
    _ = injectiveMoment H node294 := by rfl

def raw6474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 0, 0], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![2, 0, -3, 1]]

def raw6474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![0, 0, -1, 1], ![-2, 0, 3, -1]]

def raw6474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw6474step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6474 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6474 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw6474 = injectiveMoment H raw6474step0 := by
      have heq : raw6474step0 = raw6474.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6474).symm
    injectiveMoment H raw6474step0 = injectiveMoment H raw6474step1 := by
      have heq : raw6474step1 = -raw6474step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6474step0).symm
    injectiveMoment H raw6474step1 = injectiveMoment H raw6474step2 := by
      have hz : ∀ i, raw6474step1 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw6474step2 = (fun i j => raw6474step1 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6474step1 permutation15 hz
    injectiveMoment H raw6474step2 = injectiveMoment H raw6474step3 := by
      have heq : raw6474step3 = (fun i j => raw6474step2 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6474step2 permutation31 permutation4
    _ = injectiveMoment H node181 := by rfl

def raw6475 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 1, 0, -2]]

def raw6475step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2]]

def raw6475step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]

def raw6475step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw6475step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical6475 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6475 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6475 = injectiveMoment H raw6475step0 := by
      have heq : raw6475step0 = raw6475.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6475).symm
    injectiveMoment H raw6475step0 = injectiveMoment H raw6475step1 := by
      have hz : ∀ j, raw6475step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw6475step1 = (fun i j => raw6475step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6475step0 permutation21 hz
    injectiveMoment H raw6475step1 = injectiveMoment H raw6475step2 := by
      have hz : ∀ i, raw6475step1 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw6475step2 = (fun i j => raw6475step1 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6475step1 permutation5 hz
    injectiveMoment H raw6475step2 = injectiveMoment H raw6475step3 := by
      have heq : raw6475step3 = (fun i j => raw6475step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6475step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw6476 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6476step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6476 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6476 = injectiveMoment H node1048 := by
  calc
    injectiveMoment H raw6476 = injectiveMoment H raw6476step0 := by
      have hz : ∀ j, raw6476 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw6476step0 = (fun i j => raw6476 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6476 permutation80 hz
    _ = injectiveMoment H node1048 := by rfl

def raw6477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 1, -1, -1]]

def raw6477step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw6477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]

def raw6477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6477 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6477 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6477 = injectiveMoment H raw6477step0 := by
      have heq : raw6477step0 = raw6477.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6477).symm
    injectiveMoment H raw6477step0 = injectiveMoment H raw6477step1 := by
      have hz : ∀ i, raw6477step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw6477step1 = (fun i j => raw6477step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6477step0 permutation21 hz
    injectiveMoment H raw6477step1 = injectiveMoment H raw6477step2 := by
      have heq : raw6477step2 = (fun i j => raw6477step1 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6477step1 permutation27 permutation6
    _ = injectiveMoment H node287 := by rfl

def raw6478 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical6478 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6478 = injectiveMoment H node2608 := by
  rfl

def raw6479 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical6479 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6479 = injectiveMoment H node2609 := by
  rfl

def raw6480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical6480 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6480 = injectiveMoment H node2610 := by
  rfl

def raw6481 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

theorem canonical6481 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6481 = injectiveMoment H node1045 := by
  rfl

def raw6482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem canonical6482 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6482 = injectiveMoment H node2611 := by
  rfl

def raw6483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, 0, -1]]

def raw6483step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6483 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6483 = injectiveMoment H node1048 := by
  calc
    injectiveMoment H raw6483 = injectiveMoment H raw6483step0 := by
      have hz : ∀ j, raw6483 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw6483step0 = (fun i j => raw6483 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6483 permutation104 hz
    _ = injectiveMoment H node1048 := by rfl

def raw6484 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical6484 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6484 = injectiveMoment H node2612 := by
  rfl

def raw6485 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw6485step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6485 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6485 = injectiveMoment H node2725 := by
  calc
    injectiveMoment H raw6485 = injectiveMoment H raw6485step0 := by
      have heq : raw6485step0 = (fun i j => raw6485 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6485 permutation41 permutation11
    _ = injectiveMoment H node2725 := by rfl

def raw6486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6486 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6486 = injectiveMoment H node1048 := by
  rfl

def raw6487 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6487step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6487 = injectiveMoment H node2725 := by
  calc
    injectiveMoment H raw6487 = injectiveMoment H raw6487step0 := by
      have heq : raw6487step0 = (fun i j => raw6487 (permutation47 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6487 permutation47 permutation11
    _ = injectiveMoment H node2725 := by rfl

def raw6488 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6488 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6488 = injectiveMoment H node1048 := by
  calc
    injectiveMoment H raw6488 = injectiveMoment H raw6488step0 := by
      have heq : raw6488step0 = (fun i j => raw6488 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6488 permutation10 permutation15
    _ = injectiveMoment H node1048 := by rfl

def raw6489 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

theorem canonical6489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6489 = injectiveMoment H node1049 := by
  rfl

def raw6490 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw6490step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw6490step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![0, -1, 2, -1], ![-2, 1, 0, 1]]

def raw6490step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical6490 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6490 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw6490 = injectiveMoment H raw6490step0 := by
      have heq : raw6490step0 = raw6490.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6490).symm
    injectiveMoment H raw6490step0 = injectiveMoment H raw6490step1 := by
      have heq : raw6490step1 = -raw6490step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6490step0).symm
    injectiveMoment H raw6490step1 = injectiveMoment H raw6490step2 := by
      have heq : raw6490step2 = (fun i j => raw6490step1 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6490step1 permutation21 permutation19
    _ = injectiveMoment H node1000 := by rfl

def raw6491 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6491step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6491 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6491 = injectiveMoment H node1246 := by
  calc
    injectiveMoment H raw6491 = injectiveMoment H raw6491step0 := by
      have heq : raw6491step0 = (fun i j => raw6491 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6491 permutation11 permutation11
    _ = injectiveMoment H node1246 := by rfl

def raw6492 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw6492step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical6492 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6492 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw6492 = injectiveMoment H raw6492step0 := by
      have heq : raw6492step0 = (fun i j => raw6492 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6492 permutation11 permutation11
    _ = injectiveMoment H node1265 := by rfl

def raw6493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical6493 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6493 = injectiveMoment H node1050 := by
  rfl

def raw6494 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6494step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]

def raw6494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6494 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6494 = injectiveMoment H raw6494step0 := by
      have heq : raw6494step0 = raw6494.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6494).symm
    injectiveMoment H raw6494step0 = injectiveMoment H raw6494step1 := by
      have heq : raw6494step1 = (fun i j => raw6494step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6494step0 permutation27 permutation6
    _ = injectiveMoment H node287 := by rfl

def raw6495 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6495step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6495 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6495 = injectiveMoment H node2598 := by
  calc
    injectiveMoment H raw6495 = injectiveMoment H raw6495step0 := by
      have heq : raw6495step0 = (fun i j => raw6495 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6495 permutation39 permutation9
    _ = injectiveMoment H node2598 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
