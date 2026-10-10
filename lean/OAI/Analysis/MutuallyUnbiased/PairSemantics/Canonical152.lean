import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4864 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![2, -2, 0], ![1, 3, -4]]

def raw4864step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 2, -3], ![-2, 2, 0], ![-1, -3, 4]]

def raw4864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical4864 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4864 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw4864 = injectiveMoment H raw4864step0 := by
      have heq : raw4864step0 = -raw4864 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4864).symm
    injectiveMoment H raw4864step0 = injectiveMoment H raw4864step1 := by
      have heq : raw4864step1 = (fun i j => raw4864step0 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4864step0 permutation26 permutation4
    _ = injectiveMoment H node191 := by rfl

def raw4865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw4865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw4865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4865 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4865 = injectiveMoment H node2659 := by
  calc
    injectiveMoment H raw4865 = injectiveMoment H raw4865step0 := by
      have heq : raw4865step0 = -raw4865 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4865).symm
    injectiveMoment H raw4865step0 = injectiveMoment H raw4865step1 := by
      have heq : raw4865step1 = (fun i j => raw4865step0 (permutation171 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4865step0 permutation171 permutation6
    _ = injectiveMoment H node2659 := by rfl

def raw4866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical4866 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4866 = injectiveMoment H node2295 := by
  rfl

def raw4867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical4867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4867 = injectiveMoment H node2667 := by
  calc
    injectiveMoment H raw4867 = injectiveMoment H raw4867step0 := by
      have heq : raw4867step0 = (fun i j => raw4867 (permutation213 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4867 permutation213 permutation5
    _ = injectiveMoment H node2667 := by rfl

def raw4868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw4868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical4868 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4868 = injectiveMoment H node1142 := by
  calc
    injectiveMoment H raw4868 = injectiveMoment H raw4868step0 := by
      have heq : raw4868step0 = (fun i j => raw4868 (permutation72 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4868 permutation72 permutation5
    _ = injectiveMoment H node1142 := by rfl

def raw4869 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw4869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw4869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4869 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4869 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H raw4869 = injectiveMoment H raw4869step0 := by
      have heq : raw4869step0 = -raw4869 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4869).symm
    injectiveMoment H raw4869step0 = injectiveMoment H raw4869step1 := by
      have heq : raw4869step1 = (fun i j => raw4869step0 (permutation41 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4869step0 permutation41 permutation6
    _ = injectiveMoment H node1141 := by rfl

def raw4870 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw4870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw4870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical4870 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4870 = injectiveMoment H node625 := by
  calc
    injectiveMoment H raw4870 = injectiveMoment H raw4870step0 := by
      have heq : raw4870step0 = -raw4870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4870).symm
    injectiveMoment H raw4870step0 = injectiveMoment H raw4870step1 := by
      have heq : raw4870step1 = (fun i j => raw4870step0 (permutation150 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4870step0 permutation150 permutation3
    _ = injectiveMoment H node625 := by rfl

def raw4871 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw4871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical4871 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4871 = injectiveMoment H node626 := by
  calc
    injectiveMoment H raw4871 = injectiveMoment H raw4871step0 := by
      have heq : raw4871step0 = (fun i j => raw4871 (permutation102 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4871 permutation102 permutation7
    _ = injectiveMoment H node626 := by rfl

def raw4872 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw4872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical4872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4872 = injectiveMoment H node624 := by
  calc
    injectiveMoment H raw4872 = injectiveMoment H raw4872step0 := by
      have heq : raw4872step0 = (fun i j => raw4872 (permutation96 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4872 permutation96 permutation7
    _ = injectiveMoment H node624 := by rfl

def raw4873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4873 = injectiveMoment H node695 := by
  rfl

def raw4874 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]

def raw4874step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 2, -1], ![-2, -2, 4]]

def raw4874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical4874 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4874 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw4874 = injectiveMoment H raw4874step0 := by
      have heq : raw4874step0 = -raw4874 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4874).symm
    injectiveMoment H raw4874step0 = injectiveMoment H raw4874step1 := by
      have heq : raw4874step1 = (fun i j => raw4874step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4874step0 permutation32 permutation3
    _ = injectiveMoment H node134 := by rfl

def raw4875 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 3, -4]]

def raw4875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4875 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4875 = injectiveMoment H node695 := by
  calc
    injectiveMoment H raw4875 = injectiveMoment H raw4875step0 := by
      have heq : raw4875step0 = (fun i j => raw4875 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4875 permutation35 permutation3
    _ = injectiveMoment H node695 := by rfl

def raw4876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw4876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical4876 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4876 = injectiveMoment H node374 := by
  calc
    injectiveMoment H raw4876 = injectiveMoment H raw4876step0 := by
      have heq : raw4876step0 = (fun i j => raw4876 (permutation143 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4876 permutation143 permutation7
    _ = injectiveMoment H node374 := by rfl

def raw4877 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw4877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

theorem canonical4877 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4877 = injectiveMoment H node1153 := by
  calc
    injectiveMoment H raw4877 = injectiveMoment H raw4877step0 := by
      have heq : raw4877step0 = (fun i j => raw4877 (permutation65 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4877 permutation65 permutation5
    _ = injectiveMoment H node1153 := by rfl

def raw4878 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]

def raw4878step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4878 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4878 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw4878 = injectiveMoment H raw4878step0 := by
      have heq : raw4878step0 = (fun i j => raw4878 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4878 permutation19 permutation5
    _ = injectiveMoment H node276 := by rfl

def raw4879 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, -3, 1], ![1, 3, -4]]

def raw4879step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-2, 3, -1], ![-1, -3, 4]]

def raw4879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical4879 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4879 = injectiveMoment H node161 := by
  calc
    injectiveMoment H raw4879 = injectiveMoment H raw4879step0 := by
      have heq : raw4879step0 = -raw4879 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4879).symm
    injectiveMoment H raw4879step0 = injectiveMoment H raw4879step1 := by
      have heq : raw4879step1 = (fun i j => raw4879step0 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4879step0 permutation26 permutation4
    _ = injectiveMoment H node161 := by rfl

def raw4880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw4880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4880 = injectiveMoment H node2655 := by
  calc
    injectiveMoment H raw4880 = injectiveMoment H raw4880step0 := by
      have heq : raw4880step0 = (fun i j => raw4880 (permutation392 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4880 permutation392 permutation6
    _ = injectiveMoment H node2655 := by rfl

def raw4881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw4881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4881 = injectiveMoment H node2665 := by
  calc
    injectiveMoment H raw4881 = injectiveMoment H raw4881step0 := by
      have heq : raw4881step0 = (fun i j => raw4881 (permutation370 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4881 permutation370 permutation6
    _ = injectiveMoment H node2665 := by rfl

def raw4882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw4882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw4882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4882 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4882 = injectiveMoment H node2669 := by
  calc
    injectiveMoment H raw4882 = injectiveMoment H raw4882step0 := by
      have heq : raw4882step0 = -raw4882 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4882).symm
    injectiveMoment H raw4882step0 = injectiveMoment H raw4882step1 := by
      have heq : raw4882step1 = (fun i j => raw4882step0 (permutation327 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4882step0 permutation327 permutation5
    _ = injectiveMoment H node2669 := by rfl

def raw4883 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]

def raw4883step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]

def raw4883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical4883 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4883 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw4883 = injectiveMoment H raw4883step0 := by
      have hz : ∀ j, raw4883 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4883step0 = (fun i j => raw4883 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4883 permutation80 hz
    injectiveMoment H raw4883step0 = injectiveMoment H raw4883step1 := by
      have heq : raw4883step1 = (fun i j => raw4883step0 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4883step0 permutation32 permutation6
    _ = injectiveMoment H node283 := by rfl

def raw4884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw4884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw4884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4884 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4884 = injectiveMoment H node2660 := by
  calc
    injectiveMoment H raw4884 = injectiveMoment H raw4884step0 := by
      have heq : raw4884step0 = -raw4884 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4884).symm
    injectiveMoment H raw4884step0 = injectiveMoment H raw4884step1 := by
      have heq : raw4884step1 = (fun i j => raw4884step0 (permutation158 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4884step0 permutation158 permutation8
    _ = injectiveMoment H node2660 := by rfl

def raw4885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw4885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4885 = injectiveMoment H node1135 := by
  calc
    injectiveMoment H raw4885 = injectiveMoment H raw4885step0 := by
      have heq : raw4885step0 = (fun i j => raw4885 (permutation148 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4885 permutation148 permutation6
    _ = injectiveMoment H node1135 := by rfl

def raw4886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw4886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4886 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4886 = injectiveMoment H node659 := by
  calc
    injectiveMoment H raw4886 = injectiveMoment H raw4886step0 := by
      have heq : raw4886step0 = (fun i j => raw4886 (permutation148 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4886 permutation148 permutation6
    _ = injectiveMoment H node659 := by rfl

def raw4887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4887 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4887 = injectiveMoment H node710 := by
  calc
    injectiveMoment H raw4887 = injectiveMoment H raw4887step0 := by
      have heq : raw4887step0 = (fun i j => raw4887 (permutation88 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4887 permutation88 permutation5
    _ = injectiveMoment H node710 := by rfl

def raw4888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw4888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4888 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4888 = injectiveMoment H node709 := by
  calc
    injectiveMoment H raw4888 = injectiveMoment H raw4888step0 := by
      have heq : raw4888step0 = (fun i j => raw4888 (permutation144 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4888 permutation144 permutation8
    _ = injectiveMoment H node709 := by rfl

def raw4889 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw4889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical4889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4889 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw4889 = injectiveMoment H raw4889step0 := by
      have heq : raw4889step0 = -raw4889 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4889).symm
    injectiveMoment H raw4889step0 = injectiveMoment H raw4889step1 := by
      have heq : raw4889step1 = (fun i j => raw4889step0 (permutation36 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4889step0 permutation36 permutation6
    _ = injectiveMoment H node1151 := by rfl

def raw4890 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]

def raw4890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0]]

def raw4890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical4890 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4890 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw4890 = injectiveMoment H raw4890step0 := by
      have heq : raw4890step0 = -raw4890 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4890).symm
    injectiveMoment H raw4890step0 = injectiveMoment H raw4890step1 := by
      have heq : raw4890step1 = (fun i j => raw4890step0 (permutation33 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4890step0 permutation33 permutation6
    _ = injectiveMoment H node1151 := by rfl

def raw4891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]

def raw4891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical4891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4891 = injectiveMoment H node626 := by
  calc
    injectiveMoment H raw4891 = injectiveMoment H raw4891step0 := by
      have heq : raw4891step0 = (fun i j => raw4891 (permutation102 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4891 permutation102 permutation5
    _ = injectiveMoment H node626 := by rfl

def raw4892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw4892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4892 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H raw4892 = injectiveMoment H raw4892step0 := by
      have heq : raw4892step0 = (fun i j => raw4892 (permutation78 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4892 permutation78 permutation7
    _ = injectiveMoment H node1141 := by rfl

def raw4893 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4893 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw4893 = injectiveMoment H raw4893step0 := by
      have heq : raw4893step0 = (fun i j => raw4893 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4893 permutation19 permutation7
    _ = injectiveMoment H node276 := by rfl

def raw4894 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 3, -2], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def raw4894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical4894 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4894 = injectiveMoment H node532 := by
  calc
    injectiveMoment H raw4894 = injectiveMoment H raw4894step0 := by
      have heq : raw4894step0 = (fun i j => raw4894 (permutation78 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4894 permutation78 permutation7
    _ = injectiveMoment H node532 := by rfl

def raw4895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw4895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]

def raw4895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4895 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4895 = injectiveMoment H node651 := by
  calc
    injectiveMoment H raw4895 = injectiveMoment H raw4895step0 := by
      have heq : raw4895step0 = -raw4895 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4895).symm
    injectiveMoment H raw4895step0 = injectiveMoment H raw4895step1 := by
      have heq : raw4895step1 = (fun i j => raw4895step0 (permutation144 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4895step0 permutation144 permutation3
    _ = injectiveMoment H node651 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
