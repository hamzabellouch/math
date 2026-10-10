import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw704 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem canonical704 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw704 = injectiveMoment H node101 := by
  rfl

def raw705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical705 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw705 = injectiveMoment H node359 := by
  rfl

def raw706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw706 = injectiveMoment H node360 := by
  rfl

def raw707 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical707 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw707 = injectiveMoment H node361 := by
  rfl

def raw708 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

theorem canonical708 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw708 = injectiveMoment H node102 := by
  rfl

def raw709 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]

def raw709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw709 = injectiveMoment H node360 := by
  calc
    injectiveMoment H raw709 = injectiveMoment H raw709step0 := by
      have heq : raw709step0 = (fun i j => raw709 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw709 permutation35 permutation3
    _ = injectiveMoment H node360 := by rfl

def raw710 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]

def raw710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

theorem canonical710 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw710 = injectiveMoment H node666 := by
  calc
    injectiveMoment H raw710 = injectiveMoment H raw710step0 := by
      have heq : raw710step0 = (fun i j => raw710 (permutation64 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw710 permutation64 permutation5
    _ = injectiveMoment H node666 := by rfl

def raw711 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

def raw711step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw711 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw711 = injectiveMoment H raw711step0 := by
      have heq : raw711step0 = (fun i j => raw711 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw711 permutation17 permutation5
    _ = injectiveMoment H node209 := by rfl

def raw712 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]

def raw712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

theorem canonical712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw712 = injectiveMoment H node666 := by
  calc
    injectiveMoment H raw712 = injectiveMoment H raw712step0 := by
      have heq : raw712step0 = (fun i j => raw712 (permutation72 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw712 permutation72 permutation5
    _ = injectiveMoment H node666 := by rfl

def raw713 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw713step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw713 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw713 = injectiveMoment H raw713step0 := by
      have heq : raw713step0 = (fun i j => raw713 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw713 permutation19 permutation5
    _ = injectiveMoment H node212 := by rfl

def raw714 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical714 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw714 = injectiveMoment H node103 := by
  rfl

def raw715 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

theorem canonical715 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw715 = injectiveMoment H node104 := by
  rfl

def raw716 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, -2, 0], ![1, 3, -4]]

def raw716step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

theorem canonical716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw716 = injectiveMoment H node104 := by
  calc
    injectiveMoment H raw716 = injectiveMoment H raw716step0 := by
      have heq : raw716step0 = (fun i j => raw716 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw716 permutation10 permutation3
    _ = injectiveMoment H node104 := by rfl

def raw717 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, -1, -1], ![1, 2, -3]]

def raw717step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw717 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw717 = injectiveMoment H raw717step0 := by
      have heq : raw717step0 = (fun i j => raw717 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw717 permutation10 permutation3
    _ = injectiveMoment H node103 := by rfl

def raw718 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]

def raw718step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw718 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw718 = injectiveMoment H raw718step0 := by
      have heq : raw718step0 = (fun i j => raw718 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw718 permutation17 permutation5
    _ = injectiveMoment H node212 := by rfl

def raw719 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![3, 1, -4]]

def raw719step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]

def raw719step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-2, -2, 4]]

def raw719step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical719 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw719 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw719 = injectiveMoment H raw719step0 := by
      have heq : raw719step0 = raw719.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw719).symm
    injectiveMoment H raw719step0 = injectiveMoment H raw719step1 := by
      have heq : raw719step1 = -raw719step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw719step0).symm
    injectiveMoment H raw719step1 = injectiveMoment H raw719step2 := by
      have heq : raw719step2 = (fun i j => raw719step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw719step1 permutation7 permutation5
    _ = injectiveMoment H node32 := by rfl

def raw720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

theorem canonical720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw720 = injectiveMoment H node2793 := by
  calc
    injectiveMoment H raw720 = injectiveMoment H raw720step0 := by
      have heq : raw720step0 = (fun i j => raw720 (permutation209 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw720 permutation209 permutation5
    _ = injectiveMoment H node2793 := by rfl

def raw721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]

def raw721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]

def raw721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical721 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw721 = injectiveMoment H node2671 := by
  calc
    injectiveMoment H raw721 = injectiveMoment H raw721step0 := by
      have heq : raw721step0 = -raw721 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw721).symm
    injectiveMoment H raw721step0 = injectiveMoment H raw721step1 := by
      have heq : raw721step1 = (fun i j => raw721step0 (permutation324 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw721step0 permutation324 permutation5
    _ = injectiveMoment H node2671 := by rfl

def raw722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]

def raw722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]

def raw722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical722 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw722 = injectiveMoment H node1143 := by
  calc
    injectiveMoment H raw722 = injectiveMoment H raw722step0 := by
      have heq : raw722step0 = -raw722 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw722).symm
    injectiveMoment H raw722step0 = injectiveMoment H raw722step1 := by
      have heq : raw722step1 = (fun i j => raw722step0 (permutation108 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw722step0 permutation108 permutation5
    _ = injectiveMoment H node1143 := by rfl

def raw723 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]

def raw723step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]

def raw723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical723 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw723 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw723 = injectiveMoment H raw723step0 := by
      have hz : ∀ j, raw723 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw723step0 = (fun i j => raw723 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw723 permutation80 hz
    injectiveMoment H raw723step0 = injectiveMoment H raw723step1 := by
      have heq : raw723step1 = (fun i j => raw723step0 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw723step0 permutation30 permutation6
    _ = injectiveMoment H node259 := by rfl

def raw724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]

def raw724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]

def raw724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]

def raw724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical724 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw724 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw724 = injectiveMoment H raw724step0 := by
      have heq : raw724step0 = -raw724 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw724).symm
    injectiveMoment H raw724step0 = injectiveMoment H raw724step1 := by
      have hz : ∀ j, raw724step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw724step1 = (fun i j => raw724step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw724step0 permutation80 hz
    injectiveMoment H raw724step1 = injectiveMoment H raw724step2 := by
      have heq : raw724step2 = (fun i j => raw724step1 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw724step1 permutation28 permutation5
    _ = injectiveMoment H node263 := by rfl

def raw725 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]

def raw725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical725 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw725 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw725 = injectiveMoment H raw725step0 := by
      have heq : raw725step0 = -raw725 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw725).symm
    injectiveMoment H raw725step0 = injectiveMoment H raw725step1 := by
      have hz : ∀ j, raw725step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw725step1 = (fun i j => raw725step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw725step0 permutation80 hz
    injectiveMoment H raw725step1 = injectiveMoment H raw725step2 := by
      have heq : raw725step2 = (fun i j => raw725step1 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw725step1 permutation11 permutation6
    _ = injectiveMoment H node261 := by rfl

def raw726 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]

def raw726step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]

def raw726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw726 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw726 = injectiveMoment H raw726step0 := by
      have hz : ∀ j, raw726 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw726step0 = (fun i j => raw726 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw726 permutation104 hz
    injectiveMoment H raw726step0 = injectiveMoment H raw726step1 := by
      have heq : raw726step1 = (fun i j => raw726step0 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw726step0 permutation30 permutation6
    _ = injectiveMoment H node259 := by rfl

def raw727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

theorem canonical727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw727 = injectiveMoment H node1428 := by
  rfl

def raw728 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

theorem canonical728 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw728 = injectiveMoment H node364 := by
  rfl

def raw729 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical729 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw729 = injectiveMoment H node365 := by
  rfl

def raw730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical730 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw730 = injectiveMoment H node1430 := by
  rfl

def raw731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical731 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw731 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw731 = injectiveMoment H raw731step0 := by
      have heq : raw731step0 = -raw731 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw731).symm
    injectiveMoment H raw731step0 = injectiveMoment H raw731step1 := by
      have heq : raw731step1 = (fun i j => raw731step0 (permutation174 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw731step0 permutation174 permutation6
    _ = injectiveMoment H node2469 := by rfl

def raw732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]

def raw732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical732 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw732 = injectiveMoment H node869 := by
  calc
    injectiveMoment H raw732 = injectiveMoment H raw732step0 := by
      have heq : raw732step0 = -raw732 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw732).symm
    injectiveMoment H raw732step0 = injectiveMoment H raw732step1 := by
      have heq : raw732step1 = (fun i j => raw732step0 (permutation43 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw732step0 permutation43 permutation6
    _ = injectiveMoment H node869 := by rfl

def raw733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical733 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw733 = injectiveMoment H node868 := by
  calc
    injectiveMoment H raw733 = injectiveMoment H raw733step0 := by
      have heq : raw733step0 = -raw733 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw733).symm
    injectiveMoment H raw733step0 = injectiveMoment H raw733step1 := by
      have heq : raw733step1 = (fun i j => raw733step0 (permutation41 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw733step0 permutation41 permutation6
    _ = injectiveMoment H node868 := by rfl

def raw734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

theorem canonical734 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw734 = injectiveMoment H node366 := by
  rfl

def raw735 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]

def raw735step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw735 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw735 = injectiveMoment H raw735step0 := by
      have heq : raw735step0 = (fun i j => raw735 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw735 permutation30 permutation6
    _ = injectiveMoment H node259 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
