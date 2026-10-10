import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4192 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw4192step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![2, 1, -3, 0], ![0, -1, 3, -2]]

def raw4192step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-2, -1, 3, 0], ![0, 1, -3, 2]]

def raw4192step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical4192 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4192 = injectiveMoment H node799 := by
  calc
    injectiveMoment H raw4192 = injectiveMoment H raw4192step0 := by
      have heq : raw4192step0 = raw4192.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4192).symm
    injectiveMoment H raw4192step0 = injectiveMoment H raw4192step1 := by
      have heq : raw4192step1 = -raw4192step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4192step0).symm
    injectiveMoment H raw4192step1 = injectiveMoment H raw4192step2 := by
      have heq : raw4192step2 = (fun i j => raw4192step1 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4192step1 permutation23 permutation16
    _ = injectiveMoment H node799 := by rfl

def raw4193 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw4193step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical4193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4193 = injectiveMoment H node1507 := by
  calc
    injectiveMoment H raw4193 = injectiveMoment H raw4193step0 := by
      have heq : raw4193step0 = (fun i j => raw4193 (permutation125 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4193 permutation125 permutation23
    _ = injectiveMoment H node1507 := by rfl

def raw4194 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, -4, 2], ![2, -2, 2, -2]]

def raw4194step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -4, 2], ![0, 2, -2]]

def raw4194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 4, -2], ![0, -2, 2]]

def raw4194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4194 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4194 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw4194 = injectiveMoment H raw4194step0 := by
      have heq : raw4194step0 = raw4194.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4194).symm
    injectiveMoment H raw4194step0 = injectiveMoment H raw4194step1 := by
      have heq : raw4194step1 = -raw4194step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4194step0).symm
    injectiveMoment H raw4194step1 = injectiveMoment H raw4194step2 := by
      have heq : raw4194step2 = (fun i j => raw4194step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4194step1 permutation24 permutation4
    _ = injectiveMoment H node151 := by rfl

def raw4195 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, -3, 1], ![2, -2, 1, -1]]

def raw4195step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -3, 1], ![0, 1, -1]]

def raw4195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 3, -1], ![0, -1, 1]]

def raw4195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4195 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4195 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw4195 = injectiveMoment H raw4195step0 := by
      have heq : raw4195step0 = raw4195.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4195).symm
    injectiveMoment H raw4195step0 = injectiveMoment H raw4195step1 := by
      have heq : raw4195step1 = -raw4195step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4195step0).symm
    injectiveMoment H raw4195step1 = injectiveMoment H raw4195step2 := by
      have heq : raw4195step2 = (fun i j => raw4195step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4195step1 permutation26 permutation4
    _ = injectiveMoment H node177 := by rfl

def raw4196 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, -1, -1], ![2, -2, -1, 1]]

def raw4196step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![0, -1, 1]]

def raw4196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4196 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4196 = injectiveMoment H raw4196step0 := by
      have heq : raw4196step0 = raw4196.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4196).symm
    injectiveMoment H raw4196step0 = injectiveMoment H raw4196step1 := by
      have heq : raw4196step1 = (fun i j => raw4196step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4196step0 permutation13 permutation3
    _ = injectiveMoment H node203 := by rfl

def raw4197 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, 0, -2], ![2, -2, -2, 2]]

def raw4197step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, 0, -2], ![0, -2, 2]]

def raw4197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4197 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw4197 = injectiveMoment H raw4197step0 := by
      have heq : raw4197step0 = raw4197.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4197).symm
    injectiveMoment H raw4197step0 = injectiveMoment H raw4197step1 := by
      have heq : raw4197step1 = (fun i j => raw4197step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4197step0 permutation13 permutation3
    _ = injectiveMoment H node197 := by rfl

def raw4198 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, 1, -3], ![2, -2, -3, 3]]

def raw4198step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, 1, -3], ![0, -3, 3]]

def raw4198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, -1, 3], ![0, 3, -3]]

def raw4198step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4198 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4198 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw4198 = injectiveMoment H raw4198step0 := by
      have heq : raw4198step0 = raw4198.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4198).symm
    injectiveMoment H raw4198step0 = injectiveMoment H raw4198step1 := by
      have heq : raw4198step1 = -raw4198step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4198step0).symm
    injectiveMoment H raw4198step1 = injectiveMoment H raw4198step2 := by
      have heq : raw4198step2 = (fun i j => raw4198step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4198step1 permutation24 permutation3
    _ = injectiveMoment H node163 := by rfl

def raw4199 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, -4, 1], ![2, -3, 2, -1]]

def raw4199step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -4, 2], ![0, 1, -1]]

def raw4199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![-2, 4, -2], ![0, -1, 1]]

def raw4199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical4199 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4199 = injectiveMoment H node147 := by
  calc
    injectiveMoment H raw4199 = injectiveMoment H raw4199step0 := by
      have heq : raw4199step0 = raw4199.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4199).symm
    injectiveMoment H raw4199step0 = injectiveMoment H raw4199step1 := by
      have heq : raw4199step1 = -raw4199step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4199step0).symm
    injectiveMoment H raw4199step1 = injectiveMoment H raw4199step2 := by
      have heq : raw4199step2 = (fun i j => raw4199step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4199step1 permutation26 permutation4
    _ = injectiveMoment H node147 := by rfl

def raw4200 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, -2, -1], ![2, -3, 0, 1]]

def raw4200step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -2, 0], ![0, -1, 1]]

def raw4200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical4200 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4200 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw4200 = injectiveMoment H raw4200step0 := by
      have heq : raw4200step0 = raw4200.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4200).symm
    injectiveMoment H raw4200step0 = injectiveMoment H raw4200step1 := by
      have heq : raw4200step1 = (fun i j => raw4200step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4200step0 permutation13 permutation3
    _ = injectiveMoment H node204 := by rfl

def raw4201 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, -1, -2], ![2, -3, -1, 2]]

def raw4201step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -1, -1], ![0, -2, 2]]

def raw4201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4201 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4201 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw4201 = injectiveMoment H raw4201step0 := by
      have heq : raw4201step0 = raw4201.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4201).symm
    injectiveMoment H raw4201step0 = injectiveMoment H raw4201step1 := by
      have heq : raw4201step1 = (fun i j => raw4201step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4201step0 permutation13 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw4202 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, 0, -3], ![2, -3, -2, 3]]

def raw4202step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, 0, -2], ![0, -3, 3]]

def raw4202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4202 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw4202 = injectiveMoment H raw4202step0 := by
      have heq : raw4202step0 = raw4202.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4202).symm
    injectiveMoment H raw4202step0 = injectiveMoment H raw4202step1 := by
      have heq : raw4202step1 = (fun i j => raw4202step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4202step0 permutation13 permutation3
    _ = injectiveMoment H node192 := by rfl

def raw4203 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 4, -3, -1], ![2, -4, 1, 1]]

def raw4203step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![2, -3, 1], ![0, -1, 1]]

def raw4203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -4, 4], ![-2, 3, -1], ![0, 1, -1]]

def raw4203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

theorem canonical4203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4203 = injectiveMoment H node171 := by
  calc
    injectiveMoment H raw4203 = injectiveMoment H raw4203step0 := by
      have heq : raw4203step0 = raw4203.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4203).symm
    injectiveMoment H raw4203step0 = injectiveMoment H raw4203step1 := by
      have heq : raw4203step1 = -raw4203step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4203step0).symm
    injectiveMoment H raw4203step1 = injectiveMoment H raw4203step2 := by
      have heq : raw4203step2 = (fun i j => raw4203step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4203step1 permutation26 permutation4
    _ = injectiveMoment H node171 := by rfl

def raw4204 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 4, -2, -2], ![2, -4, 0, 2]]

def raw4204step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![2, -2, 0], ![0, -2, 2]]

def raw4204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

theorem canonical4204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4204 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw4204 = injectiveMoment H raw4204step0 := by
      have heq : raw4204step0 = raw4204.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4204).symm
    injectiveMoment H raw4204step0 = injectiveMoment H raw4204step1 := by
      have heq : raw4204step1 = (fun i j => raw4204step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4204step0 permutation13 permutation3
    _ = injectiveMoment H node199 := by rfl

def raw4205 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -3, 1, 1], ![1, 3, -3, -1]]

def raw4205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 1, -3], ![0, 1, -1]]

def raw4205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -1, 3], ![0, -1, 1]]

def raw4205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4205 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4205 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw4205 = injectiveMoment H raw4205step0 := by
      have heq : raw4205step0 = raw4205.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4205).symm
    injectiveMoment H raw4205step0 = injectiveMoment H raw4205step1 := by
      have heq : raw4205step1 = -raw4205step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4205step0).symm
    injectiveMoment H raw4205step1 = injectiveMoment H raw4205step2 := by
      have heq : raw4205step2 = (fun i j => raw4205step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4205step1 permutation26 permutation3
    _ = injectiveMoment H node170 := by rfl

def raw4206 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, -3, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw4206step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![2, -3, 1, 0], ![0, 4, -2, -2]]

def raw4206step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, 0, -2]]

theorem canonical4206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4206 = injectiveMoment H node403 := by
  calc
    injectiveMoment H raw4206 = injectiveMoment H raw4206step0 := by
      have heq : raw4206step0 = raw4206.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4206).symm
    injectiveMoment H raw4206step0 = injectiveMoment H raw4206step1 := by
      have heq : raw4206step1 = (fun i j => raw4206step0 (permutation28 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4206step0 permutation28 permutation25
    _ = injectiveMoment H node403 := by rfl

def raw4207 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, -1, 2], ![1, 2, -1, -2]]

def raw4207step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![0, 2, -2]]

def raw4207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4207 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4207 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw4207 = injectiveMoment H raw4207step0 := by
      have heq : raw4207step0 = raw4207.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4207).symm
    injectiveMoment H raw4207step0 = injectiveMoment H raw4207step1 := by
      have heq : raw4207step1 = (fun i j => raw4207step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4207step0 permutation10 permutation3
    _ = injectiveMoment H node224 := by rfl

def raw4208 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, 0, 1], ![1, 2, -2, -1]]

def raw4208step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1]]

def raw4208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, 0, 2], ![0, -1, 1]]

def raw4208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4208 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4208 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4208 = injectiveMoment H raw4208step0 := by
      have heq : raw4208step0 = raw4208.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4208).symm
    injectiveMoment H raw4208step0 = injectiveMoment H raw4208step1 := by
      have heq : raw4208step1 = -raw4208step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4208step0).symm
    injectiveMoment H raw4208step1 = injectiveMoment H raw4208step2 := by
      have heq : raw4208step2 = (fun i j => raw4208step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4208step1 permutation26 permutation3
    _ = injectiveMoment H node203 := by rfl

def raw4209 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, 2, -1], ![1, 2, -4, 1]]

def raw4209step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 2, -4], ![0, -1, 1]]

def raw4209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -2, 4], ![0, 1, -1]]

def raw4209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4209 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4209 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw4209 = injectiveMoment H raw4209step0 := by
      have heq : raw4209step0 = raw4209.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4209).symm
    injectiveMoment H raw4209step0 = injectiveMoment H raw4209step1 := by
      have heq : raw4209step1 = -raw4209step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4209step0).symm
    injectiveMoment H raw4209step1 = injectiveMoment H raw4209step2 := by
      have heq : raw4209step2 = (fun i j => raw4209step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4209step1 permutation26 permutation3
    _ = injectiveMoment H node146 := by rfl

def raw4210 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, 2, -1, -2], ![1, -2, -1, 2]]

def raw4210step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![0, -2, 2]]

def raw4210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4210 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw4210 = injectiveMoment H raw4210step0 := by
      have heq : raw4210step0 = raw4210.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4210).symm
    injectiveMoment H raw4210step0 = injectiveMoment H raw4210step1 := by
      have heq : raw4210step1 = (fun i j => raw4210step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4210step0 permutation13 permutation3
    _ = injectiveMoment H node224 := by rfl

def raw4211 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, 2, 0, -3], ![1, -2, -2, 3]]

def raw4211step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, 0, -2], ![0, -3, 3]]

def raw4211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -2, 2], ![-2, 0, 2], ![0, 3, -3]]

def raw4211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4211 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4211 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw4211 = injectiveMoment H raw4211step0 := by
      have heq : raw4211step0 = raw4211.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4211).symm
    injectiveMoment H raw4211step0 = injectiveMoment H raw4211step1 := by
      have heq : raw4211step1 = -raw4211step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4211step0).symm
    injectiveMoment H raw4211step1 = injectiveMoment H raw4211step2 := by
      have heq : raw4211step2 = (fun i j => raw4211step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4211step1 permutation24 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw4212 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![-2, 2, -2, 2], ![4, -2, -1, -1]]

def raw4212step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![3, -2, -1], ![-1, 2, -1]]

def raw4212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-3, 2, 1], ![1, -2, 1]]

def raw4212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

theorem canonical4212 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4212 = injectiveMoment H node112 := by
  calc
    injectiveMoment H raw4212 = injectiveMoment H raw4212step0 := by
      have heq : raw4212step0 = raw4212.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4212).symm
    injectiveMoment H raw4212step0 = injectiveMoment H raw4212step1 := by
      have heq : raw4212step1 = -raw4212step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4212step0).symm
    injectiveMoment H raw4212step1 = injectiveMoment H raw4212step2 := by
      have heq : raw4212step2 = (fun i j => raw4212step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4212step1 permutation24 permutation4
    _ = injectiveMoment H node112 := by rfl

def raw4213 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![-1, 2, -2, 1], ![3, -2, -1, 0]]

def raw4213step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![3, -2, -1], ![-1, 1, 0]]

def raw4213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-3, 2, 1], ![1, -1, 0]]

def raw4213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical4213 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4213 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw4213 = injectiveMoment H raw4213step0 := by
      have heq : raw4213step0 = raw4213.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4213).symm
    injectiveMoment H raw4213step0 = injectiveMoment H raw4213step1 := by
      have heq : raw4213step1 = -raw4213step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4213step0).symm
    injectiveMoment H raw4213step1 = injectiveMoment H raw4213step2 := by
      have heq : raw4213step2 = (fun i j => raw4213step1 (permutation14 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4213step1 permutation14 permutation8
    _ = injectiveMoment H node107 := by rfl

def raw4214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical4214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4214 = injectiveMoment H node2144 := by
  rfl

def raw4215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4215step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical4215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4215 = injectiveMoment H node2682 := by
  calc
    injectiveMoment H raw4215 = injectiveMoment H raw4215step0 := by
      have heq : raw4215step0 = (fun i j => raw4215 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4215 permutation60 permutation15
    _ = injectiveMoment H node2682 := by rfl

def raw4216 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4216step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 3, -4], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw4216step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical4216 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4216 = injectiveMoment H node2011 := by
  calc
    injectiveMoment H raw4216 = injectiveMoment H raw4216step0 := by
      have heq : raw4216step0 = -raw4216 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4216).symm
    injectiveMoment H raw4216step0 = injectiveMoment H raw4216step1 := by
      have heq : raw4216step1 = (fun i j => raw4216step0 (permutation99 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4216step0 permutation99 permutation15
    _ = injectiveMoment H node2011 := by rfl

def raw4217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw4217step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![3, -3, 0, 0], ![-1, 4, 0, -3]]

def raw4217step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-3, 3, 0, 0], ![1, -4, 0, 3]]

def raw4217step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -3, 3], ![0, 3, 1, -4], ![1, -2, 0, 1]]

theorem canonical4217 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4217 = injectiveMoment H node1158 := by
  calc
    injectiveMoment H raw4217 = injectiveMoment H raw4217step0 := by
      have heq : raw4217step0 = raw4217.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4217).symm
    injectiveMoment H raw4217step0 = injectiveMoment H raw4217step1 := by
      have heq : raw4217step1 = -raw4217step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4217step0).symm
    injectiveMoment H raw4217step1 = injectiveMoment H raw4217step2 := by
      have heq : raw4217step2 = (fun i j => raw4217step1 (permutation12 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4217step1 permutation12 permutation25
    _ = injectiveMoment H node1158 := by rfl

def raw4218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw4218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![3, -3, 0, 0], ![-1, 4, -1, -2]]

def raw4218step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical4218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4218 = injectiveMoment H node780 := by
  calc
    injectiveMoment H raw4218 = injectiveMoment H raw4218step0 := by
      have heq : raw4218step0 = raw4218.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4218).symm
    injectiveMoment H raw4218step0 = injectiveMoment H raw4218step1 := by
      have heq : raw4218step1 = (fun i j => raw4218step0 (permutation32 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4218step0 permutation32 permutation25
    _ = injectiveMoment H node780 := by rfl

def raw4219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical4219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4219 = injectiveMoment H node2145 := by
  rfl

def raw4220 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4220step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical4220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4220 = injectiveMoment H node2698 := by
  calc
    injectiveMoment H raw4220 = injectiveMoment H raw4220step0 := by
      have heq : raw4220step0 = (fun i j => raw4220 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4220 permutation60 permutation15
    _ = injectiveMoment H node2698 := by rfl

def raw4221 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4221step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 2, -3], ![0, -2, 0, 2], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw4221step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem canonical4221 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4221 = injectiveMoment H node2012 := by
  calc
    injectiveMoment H raw4221 = injectiveMoment H raw4221step0 := by
      have heq : raw4221step0 = -raw4221 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4221).symm
    injectiveMoment H raw4221step0 = injectiveMoment H raw4221step1 := by
      have heq : raw4221step1 = (fun i j => raw4221step0 (permutation99 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4221step0 permutation99 permutation15
    _ = injectiveMoment H node2012 := by rfl

def raw4222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw4222step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 2, -3], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw4222step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem canonical4222 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4222 = injectiveMoment H node494 := by
  calc
    injectiveMoment H raw4222 = injectiveMoment H raw4222step0 := by
      have heq : raw4222step0 = -raw4222 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4222).symm
    injectiveMoment H raw4222step0 = injectiveMoment H raw4222step1 := by
      have heq : raw4222step1 = (fun i j => raw4222step0 (permutation28 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4222step0 permutation28 permutation15
    _ = injectiveMoment H node494 := by rfl

def raw4223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 2, -3], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw4223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

theorem canonical4223 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4223 = injectiveMoment H node1001 := by
  calc
    injectiveMoment H raw4223 = injectiveMoment H raw4223step0 := by
      have heq : raw4223step0 = -raw4223 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4223).symm
    injectiveMoment H raw4223step0 = injectiveMoment H raw4223step1 := by
      have heq : raw4223step1 = (fun i j => raw4223step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4223step0 permutation31 permutation15
    _ = injectiveMoment H node1001 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
