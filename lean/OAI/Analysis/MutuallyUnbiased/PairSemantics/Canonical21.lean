import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw672 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]

def raw672step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical672 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw672 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw672 = injectiveMoment H raw672step0 := by
      have heq : raw672step0 = -raw672 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw672).symm
    injectiveMoment H raw672step0 = injectiveMoment H raw672step1 := by
      have heq : raw672step1 = (fun i j => raw672step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw672step0 permutation9 permutation8
    _ = injectiveMoment H node175 := by rfl

def raw673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical673 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw673 = injectiveMoment H node1863 := by
  calc
    injectiveMoment H raw673 = injectiveMoment H raw673step0 := by
      have heq : raw673step0 = -raw673 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw673).symm
    injectiveMoment H raw673step0 = injectiveMoment H raw673step1 := by
      have heq : raw673step1 = (fun i j => raw673step0 (permutation175 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw673step0 permutation175 permutation8
    _ = injectiveMoment H node1863 := by rfl

def raw674 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]

def raw674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]

def raw674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical674 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw674 = injectiveMoment H node533 := by
  calc
    injectiveMoment H raw674 = injectiveMoment H raw674step0 := by
      have heq : raw674step0 = -raw674 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw674).symm
    injectiveMoment H raw674step0 = injectiveMoment H raw674step1 := by
      have heq : raw674step1 = (fun i j => raw674step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw674step0 permutation41 permutation8
    _ = injectiveMoment H node533 := by rfl

def raw675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw675 = injectiveMoment H node1868 := by
  calc
    injectiveMoment H raw675 = injectiveMoment H raw675step0 := by
      have heq : raw675step0 = -raw675 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw675).symm
    injectiveMoment H raw675step0 = injectiveMoment H raw675step1 := by
      have heq : raw675step1 = (fun i j => raw675step0 (permutation169 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw675step0 permutation169 permutation8
    _ = injectiveMoment H node1868 := by rfl

def raw676 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]

def raw676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]

def raw676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

theorem canonical676 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw676 = injectiveMoment H node536 := by
  calc
    injectiveMoment H raw676 = injectiveMoment H raw676step0 := by
      have heq : raw676step0 = -raw676 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw676).symm
    injectiveMoment H raw676step0 = injectiveMoment H raw676step1 := by
      have heq : raw676step1 = (fun i j => raw676step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw676step0 permutation41 permutation8
    _ = injectiveMoment H node536 := by rfl

def raw677 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]

def raw677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]

def raw677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical677 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw677 = injectiveMoment H node539 := by
  calc
    injectiveMoment H raw677 = injectiveMoment H raw677step0 := by
      have heq : raw677step0 = -raw677 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw677).symm
    injectiveMoment H raw677step0 = injectiveMoment H raw677step1 := by
      have heq : raw677step1 = (fun i j => raw677step0 (permutation39 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw677step0 permutation39 permutation8
    _ = injectiveMoment H node539 := by rfl

def raw678 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]

def raw678step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw678 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw678 = injectiveMoment H raw678step0 := by
      have heq : raw678step0 = (fun i j => raw678 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw678 permutation30 permutation8
    _ = injectiveMoment H node159 := by rfl

def raw679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical679 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw679 = injectiveMoment H node1890 := by
  calc
    injectiveMoment H raw679 = injectiveMoment H raw679step0 := by
      have heq : raw679step0 = -raw679 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw679).symm
    injectiveMoment H raw679step0 = injectiveMoment H raw679step1 := by
      have heq : raw679step1 = (fun i j => raw679step0 (permutation171 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw679step0 permutation171 permutation8
    _ = injectiveMoment H node1890 := by rfl

def raw680 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]

def raw680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical680 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw680 = injectiveMoment H node569 := by
  calc
    injectiveMoment H raw680 = injectiveMoment H raw680step0 := by
      have heq : raw680step0 = -raw680 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw680).symm
    injectiveMoment H raw680step0 = injectiveMoment H raw680step1 := by
      have heq : raw680step1 = (fun i j => raw680step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw680step0 permutation41 permutation8
    _ = injectiveMoment H node569 := by rfl

def raw681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical681 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw681 = injectiveMoment H node572 := by
  calc
    injectiveMoment H raw681 = injectiveMoment H raw681step0 := by
      have heq : raw681step0 = -raw681 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw681).symm
    injectiveMoment H raw681step0 = injectiveMoment H raw681step1 := by
      have heq : raw681step1 = (fun i j => raw681step0 (permutation43 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw681step0 permutation43 permutation8
    _ = injectiveMoment H node572 := by rfl

def raw682 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]

def raw682step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical682 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw682 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw682 = injectiveMoment H raw682step0 := by
      have heq : raw682step0 = (fun i j => raw682 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw682 permutation25 permutation6
    _ = injectiveMoment H node103 := by rfl

def raw683 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]

def raw683step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical683 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw683 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw683 = injectiveMoment H raw683step0 := by
      have heq : raw683step0 = -raw683 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw683).symm
    injectiveMoment H raw683step0 = injectiveMoment H raw683step1 := by
      have heq : raw683step1 = (fun i j => raw683step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw683step0 permutation11 permutation8
    _ = injectiveMoment H node184 := by rfl

def raw684 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

theorem canonical684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw684 = injectiveMoment H node348 := by
  calc
    injectiveMoment H raw684 = injectiveMoment H raw684step0 := by
      have heq : raw684step0 = (fun i j => raw684 (permutation68 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw684 permutation68 permutation5
    _ = injectiveMoment H node348 := by rfl

def raw685 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

theorem canonical685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw685 = injectiveMoment H node344 := by
  calc
    injectiveMoment H raw685 = injectiveMoment H raw685step0 := by
      have heq : raw685step0 = (fun i j => raw685 (permutation72 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw685 permutation72 permutation5
    _ = injectiveMoment H node344 := by rfl

def raw686 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

theorem canonical686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw686 = injectiveMoment H node342 := by
  calc
    injectiveMoment H raw686 = injectiveMoment H raw686step0 := by
      have heq : raw686step0 = (fun i j => raw686 (permutation64 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw686 permutation64 permutation5
    _ = injectiveMoment H node342 := by rfl

def raw687 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![1, 0, -1], ![2, 2, -4]]

def raw687step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]

theorem canonical687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw687 = injectiveMoment H node94 := by
  calc
    injectiveMoment H raw687 = injectiveMoment H raw687step0 := by
      have heq : raw687step0 = (fun i j => raw687 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw687 permutation17 permutation5
    _ = injectiveMoment H node94 := by rfl

def raw688 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![1, 2, -3], ![2, 0, -2]]

def raw688step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

theorem canonical688 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw688 = injectiveMoment H node96 := by
  calc
    injectiveMoment H raw688 = injectiveMoment H raw688step0 := by
      have heq : raw688step0 = (fun i j => raw688 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw688 permutation19 permutation5
    _ = injectiveMoment H node96 := by rfl

def raw689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

theorem canonical689 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw689 = injectiveMoment H node1415 := by
  rfl

def raw690 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 1, -3]]

def raw690step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

def raw690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical690 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw690 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw690 = injectiveMoment H raw690step0 := by
      have hz : ∀ j, raw690 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw690step0 = (fun i j => raw690 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw690 permutation80 hz
    injectiveMoment H raw690step0 = injectiveMoment H raw690step1 := by
      have heq : raw690step1 = (fun i j => raw690step0 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw690step0 permutation17 permutation5
    _ = injectiveMoment H node209 := by rfl

def raw691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem canonical691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw691 = injectiveMoment H node1417 := by
  rfl

def raw692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw692 = injectiveMoment H node1418 := by
  rfl

def raw693 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

theorem canonical693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw693 = injectiveMoment H node354 := by
  rfl

def raw694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical694 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw694 = injectiveMoment H node1419 := by
  rfl

def raw695 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw695 = injectiveMoment H node355 := by
  rfl

def raw696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

theorem canonical696 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw696 = injectiveMoment H node2141 := by
  calc
    injectiveMoment H raw696 = injectiveMoment H raw696step0 := by
      have heq : raw696step0 = (fun i j => raw696 (permutation213 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw696 permutation213 permutation5
    _ = injectiveMoment H node2141 := by rfl

def raw697 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

theorem canonical697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw697 = injectiveMoment H node669 := by
  calc
    injectiveMoment H raw697 = injectiveMoment H raw697step0 := by
      have heq : raw697step0 = (fun i j => raw697 (permutation72 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw697 permutation72 permutation5
    _ = injectiveMoment H node669 := by rfl

def raw698 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical698 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw698 = injectiveMoment H node356 := by
  rfl

def raw699 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]

def raw699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw699 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw699 = injectiveMoment H raw699step0 := by
      have heq : raw699step0 = (fun i j => raw699 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw699 permutation19 permutation5
    _ = injectiveMoment H node214 := by rfl

def raw700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem canonical700 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw700 = injectiveMoment H node1420 := by
  rfl

def raw701 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical701 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw701 = injectiveMoment H node357 := by
  rfl

def raw702 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical702 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw702 = injectiveMoment H node358 := by
  rfl

def raw703 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1]]

def raw703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw703 = injectiveMoment H node358 := by
  calc
    injectiveMoment H raw703 = injectiveMoment H raw703step0 := by
      have heq : raw703step0 = (fun i j => raw703 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw703 permutation34 permutation3
    _ = injectiveMoment H node358 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
