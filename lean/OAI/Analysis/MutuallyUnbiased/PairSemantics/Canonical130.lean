import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4160 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]

def raw4160step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]

def raw4160step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

def raw4161 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]

def raw4161step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -2, 3], ![-1, 2, -1]]

def raw4161step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4161 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4161 = injectiveMoment H raw4161step0 := by
      have heq : raw4161step0 = -raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4161).symm
    injectiveMoment H raw4161step0 = injectiveMoment H raw4161step1 := by
      have heq : raw4161step1 = (fun i j => raw4161step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4161step0 permutation5 permutation5
    _ = injectiveMoment H node36 := by rfl

def raw4162 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 3, -4], ![1, -3, 2]]

def raw4162step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 3, -3], ![2, -4, 2]]

def raw4162step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -3, 3], ![-2, 4, -2]]

def raw4162step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4162 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4162 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4162 = injectiveMoment H raw4162step0 := by
      have heq : raw4162step0 = raw4162.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4162).symm
    injectiveMoment H raw4162step0 = injectiveMoment H raw4162step1 := by
      have heq : raw4162step1 = -raw4162step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4162step0).symm
    injectiveMoment H raw4162step1 = injectiveMoment H raw4162step2 := by
      have heq : raw4162step2 = (fun i j => raw4162step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4162step1 permutation8 permutation4
    _ = injectiveMoment H node32 := by rfl

def raw4163 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 4, -5], ![1, -4, 3]]

def raw4163step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 4, -4], ![2, -5, 3]]

def raw4163step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -4, 4], ![-2, 5, -3]]

def raw4163step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

theorem canonical4163 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4163 = injectiveMoment H node29 := by
  calc
    injectiveMoment H raw4163 = injectiveMoment H raw4163step0 := by
      have heq : raw4163step0 = raw4163.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4163).symm
    injectiveMoment H raw4163step0 = injectiveMoment H raw4163step1 := by
      have heq : raw4163step1 = -raw4163step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4163step0).symm
    injectiveMoment H raw4163step1 = injectiveMoment H raw4163step2 := by
      have heq : raw4163step2 = (fun i j => raw4163step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4163step1 permutation8 permutation4
    _ = injectiveMoment H node29 := by rfl

def raw4164 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-3, 2, -1, 2], ![5, -2, -1, -2]]

def raw4164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, -1, -1], ![0, 2, -2]]

def raw4164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4164 = injectiveMoment H node125 := by
  calc
    injectiveMoment H raw4164 = injectiveMoment H raw4164step0 := by
      have heq : raw4164step0 = raw4164.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4164).symm
    injectiveMoment H raw4164step0 = injectiveMoment H raw4164step1 := by
      have heq : raw4164step1 = (fun i j => raw4164step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4164step0 permutation10 permutation3
    _ = injectiveMoment H node125 := by rfl

def raw4165 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 2, -2, 2], ![4, -2, 0, -2]]

def raw4165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, -2, 0], ![0, 2, -2]]

def raw4165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4165 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw4165 = injectiveMoment H raw4165step0 := by
      have heq : raw4165step0 = raw4165.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4165).symm
    injectiveMoment H raw4165step0 = injectiveMoment H raw4165step1 := by
      have heq : raw4165step1 = (fun i j => raw4165step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4165step0 permutation10 permutation3
    _ = injectiveMoment H node151 := by rfl

def raw4166 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 2, -1, 1], ![4, -2, -1, -1]]

def raw4166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, -1, -1], ![0, 1, -1]]

def raw4166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4166 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4166 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw4166 = injectiveMoment H raw4166step0 := by
      have heq : raw4166step0 = raw4166.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4166).symm
    injectiveMoment H raw4166step0 = injectiveMoment H raw4166step1 := by
      have heq : raw4166step1 = (fun i j => raw4166step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4166step0 permutation13 permutation3
    _ = injectiveMoment H node146 := by rfl

def raw4167 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 2, 1, -1], ![4, -2, -3, 1]]

def raw4167step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 1, -3], ![0, -1, 1]]

def raw4167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

theorem canonical4167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4167 = injectiveMoment H node140 := by
  calc
    injectiveMoment H raw4167 = injectiveMoment H raw4167step0 := by
      have heq : raw4167step0 = raw4167.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4167).symm
    injectiveMoment H raw4167step0 = injectiveMoment H raw4167step1 := by
      have heq : raw4167step1 = (fun i j => raw4167step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4167step0 permutation13 permutation3
    _ = injectiveMoment H node140 := by rfl

def raw4168 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 3, 0, -1], ![4, -3, -2, 1]]

def raw4168step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, 0, -2], ![0, -1, 1]]

def raw4168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4168 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4168 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw4168 = injectiveMoment H raw4168step0 := by
      have heq : raw4168step0 = raw4168.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4168).symm
    injectiveMoment H raw4168step0 = injectiveMoment H raw4168step1 := by
      have heq : raw4168step1 = (fun i j => raw4168step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4168step0 permutation13 permutation3
    _ = injectiveMoment H node141 := by rfl

def raw4169 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, -2, 0, 3], ![3, 2, -2, -3]]

def raw4169step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 0, -2], ![0, 3, -3]]

def raw4169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4169 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw4169 = injectiveMoment H raw4169step0 := by
      have heq : raw4169step0 = raw4169.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4169).symm
    injectiveMoment H raw4169step0 = injectiveMoment H raw4169step1 := by
      have heq : raw4169step1 = (fun i j => raw4169step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4169step0 permutation10 permutation3
    _ = injectiveMoment H node163 := by rfl

def raw4170 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, -2, 1, 2], ![3, 2, -3, -2]]

def raw4170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 1, -3], ![0, 2, -2]]

def raw4170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical4170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4170 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw4170 = injectiveMoment H raw4170step0 := by
      have heq : raw4170step0 = raw4170.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4170).symm
    injectiveMoment H raw4170step0 = injectiveMoment H raw4170step1 := by
      have heq : raw4170step1 = (fun i j => raw4170step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4170step0 permutation10 permutation3
    _ = injectiveMoment H node162 := by rfl

def raw4171 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 2, -2, 1], ![3, -2, 0, -1]]

def raw4171step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -2, 0], ![0, 1, -1]]

def raw4171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4171 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw4171 = injectiveMoment H raw4171step0 := by
      have heq : raw4171step0 = raw4171.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4171).symm
    injectiveMoment H raw4171step0 = injectiveMoment H raw4171step1 := by
      have heq : raw4171step1 = (fun i j => raw4171step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4171step0 permutation13 permutation3
    _ = injectiveMoment H node177 := by rfl

def raw4172 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 2, 0, -1], ![3, -2, -2, 1]]

def raw4172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, 0, -2], ![0, -1, 1]]

def raw4172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4172 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw4172 = injectiveMoment H raw4172step0 := by
      have heq : raw4172step0 = raw4172.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4172).symm
    injectiveMoment H raw4172step0 = injectiveMoment H raw4172step1 := by
      have heq : raw4172step1 = (fun i j => raw4172step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4172step0 permutation13 permutation3
    _ = injectiveMoment H node169 := by rfl

def raw4173 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 2, 1, -2], ![3, -2, -3, 2]]

def raw4173step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, 1, -3], ![0, -2, 2]]

def raw4173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical4173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4173 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw4173 = injectiveMoment H raw4173step0 := by
      have heq : raw4173step0 = raw4173.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4173).symm
    injectiveMoment H raw4173step0 = injectiveMoment H raw4173step1 := by
      have heq : raw4173step1 = (fun i j => raw4173step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4173step0 permutation13 permutation3
    _ = injectiveMoment H node162 := by rfl

def raw4174 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 3, -1, -1], ![3, -3, -1, 1]]

def raw4174step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -1, -1], ![0, -1, 1]]

def raw4174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4174 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4174 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw4174 = injectiveMoment H raw4174step0 := by
      have heq : raw4174step0 = raw4174.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4174).symm
    injectiveMoment H raw4174step0 = injectiveMoment H raw4174step1 := by
      have heq : raw4174step1 = (fun i j => raw4174step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4174step0 permutation13 permutation3
    _ = injectiveMoment H node170 := by rfl

def raw4175 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 3, 0, -2], ![3, -3, -2, 2]]

def raw4175step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, 0, -2], ![0, -2, 2]]

def raw4175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4175 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4175 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw4175 = injectiveMoment H raw4175step0 := by
      have heq : raw4175step0 = raw4175.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4175).symm
    injectiveMoment H raw4175step0 = injectiveMoment H raw4175step1 := by
      have heq : raw4175step1 = (fun i j => raw4175step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4175step0 permutation13 permutation3
    _ = injectiveMoment H node163 := by rfl

def raw4176 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 4, -2, -1], ![3, -4, 0, 1]]

def raw4176step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -2, 0], ![0, -1, 1]]

def raw4176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

theorem canonical4176 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4176 = injectiveMoment H node171 := by
  calc
    injectiveMoment H raw4176 = injectiveMoment H raw4176step0 := by
      have heq : raw4176step0 = raw4176.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4176).symm
    injectiveMoment H raw4176step0 = injectiveMoment H raw4176step1 := by
      have heq : raw4176step1 = (fun i j => raw4176step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4176step0 permutation13 permutation3
    _ = injectiveMoment H node171 := by rfl

def raw4177 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -3, 0, 3], ![2, 3, -2, -3]]

def raw4177step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 0, -2], ![0, 3, -3]]

def raw4177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4177 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw4177 = injectiveMoment H raw4177step0 := by
      have heq : raw4177step0 = raw4177.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4177).symm
    injectiveMoment H raw4177step0 = injectiveMoment H raw4177step1 := by
      have heq : raw4177step1 = (fun i j => raw4177step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4177step0 permutation10 permutation3
    _ = injectiveMoment H node192 := by rfl

def raw4178 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -3, 2, 1], ![2, 3, -4, -1]]

def raw4178step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 2, -4], ![0, 1, -1]]

def raw4178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![-2, -2, 4], ![0, -1, 1]]

def raw4178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4178 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw4178 = injectiveMoment H raw4178step0 := by
      have heq : raw4178step0 = raw4178.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4178).symm
    injectiveMoment H raw4178step0 = injectiveMoment H raw4178step1 := by
      have heq : raw4178step1 = -raw4178step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4178step0).symm
    injectiveMoment H raw4178step1 = injectiveMoment H raw4178step2 := by
      have heq : raw4178step2 = (fun i j => raw4178step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4178step1 permutation26 permutation3
    _ = injectiveMoment H node141 := by rfl

def raw4179 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, -2, 4], ![2, 2, 0, -4]]

def raw4179step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, -2, 0], ![0, 4, -4]]

def raw4179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

theorem canonical4179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4179 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw4179 = injectiveMoment H raw4179step0 := by
      have heq : raw4179step0 = raw4179.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4179).symm
    injectiveMoment H raw4179step0 = injectiveMoment H raw4179step1 := by
      have heq : raw4179step1 = (fun i j => raw4179step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4179step0 permutation10 permutation3
    _ = injectiveMoment H node199 := by rfl

def raw4180 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, -1, 3], ![2, 2, -1, -3]]

def raw4180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, -1, -1], ![0, 3, -3]]

def raw4180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4180 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw4180 = injectiveMoment H raw4180step0 := by
      have heq : raw4180step0 = raw4180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4180).symm
    injectiveMoment H raw4180step0 = injectiveMoment H raw4180step1 := by
      have heq : raw4180step1 = (fun i j => raw4180step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4180step0 permutation10 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw4181 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, 0, 2], ![2, 2, -2, -2]]

def raw4181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 0, -2], ![0, 2, -2]]

def raw4181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4181 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw4181 = injectiveMoment H raw4181step0 := by
      have heq : raw4181step0 = raw4181.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4181).symm
    injectiveMoment H raw4181step0 = injectiveMoment H raw4181step1 := by
      have heq : raw4181step1 = (fun i j => raw4181step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4181step0 permutation10 permutation3
    _ = injectiveMoment H node197 := by rfl

def raw4182 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, 1, 1], ![2, 2, -3, -1]]

def raw4182step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 1, -3], ![0, 1, -1]]

def raw4182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -1, 3], ![0, -1, 1]]

def raw4182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4182 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4182 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw4182 = injectiveMoment H raw4182step0 := by
      have heq : raw4182step0 = raw4182.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4182).symm
    injectiveMoment H raw4182step0 = injectiveMoment H raw4182step1 := by
      have heq : raw4182step1 = -raw4182step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4182step0).symm
    injectiveMoment H raw4182step1 = injectiveMoment H raw4182step2 := by
      have heq : raw4182step2 = (fun i j => raw4182step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4182step1 permutation26 permutation3
    _ = injectiveMoment H node169 := by rfl

def raw4183 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, 3, -1], ![2, 2, -5, 1]]

def raw4183step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 3, -5], ![0, -1, 1]]

def raw4183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -3, 5], ![0, 1, -1]]

def raw4183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4183 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4183 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw4183 = injectiveMoment H raw4183step0 := by
      have heq : raw4183step0 = raw4183.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4183).symm
    injectiveMoment H raw4183step0 = injectiveMoment H raw4183step1 := by
      have heq : raw4183step1 = -raw4183step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4183step0).symm
    injectiveMoment H raw4183step1 = injectiveMoment H raw4183step2 := by
      have heq : raw4183step2 = (fun i j => raw4183step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4183step1 permutation26 permutation3
    _ = injectiveMoment H node120 := by rfl

def raw4184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical4184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4184 = injectiveMoment H node1164 := by
  calc
    injectiveMoment H raw4184 = injectiveMoment H raw4184step0 := by
      have heq : raw4184step0 = (fun i j => raw4184 (permutation16 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4184 permutation16 permutation15
    _ = injectiveMoment H node1164 := by rfl

def raw4185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -3, 4], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw4185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -2, 0], ![0, 1, 3, -4], ![-1, 0, -1, 2], ![-1, -1, 0, 2]]

def raw4185step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem canonical4185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4185 = injectiveMoment H node997 := by
  calc
    injectiveMoment H raw4185 = injectiveMoment H raw4185step0 := by
      have heq : raw4185step0 = -raw4185 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4185).symm
    injectiveMoment H raw4185step0 = injectiveMoment H raw4185step1 := by
      have heq : raw4185step1 = (fun i j => raw4185step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4185step0 permutation31 permutation15
    _ = injectiveMoment H node997 := by rfl

def raw4186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4186step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical4186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4186 = injectiveMoment H node1008 := by
  calc
    injectiveMoment H raw4186 = injectiveMoment H raw4186step0 := by
      have heq : raw4186step0 = (fun i j => raw4186 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4186 permutation19 permutation17
    _ = injectiveMoment H node1008 := by rfl

def raw4187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical4187 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4187 = injectiveMoment H node1002 := by
  calc
    injectiveMoment H raw4187 = injectiveMoment H raw4187step0 := by
      have heq : raw4187step0 = (fun i j => raw4187 (permutation17 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4187 permutation17 permutation17
    _ = injectiveMoment H node1002 := by rfl

def raw4188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4188step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical4188 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4188 = injectiveMoment H node1845 := by
  calc
    injectiveMoment H raw4188 = injectiveMoment H raw4188step0 := by
      have heq : raw4188step0 = (fun i j => raw4188 (permutation129 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4188 permutation129 permutation19
    _ = injectiveMoment H node1845 := by rfl

def raw4189 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4189step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical4189 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4189 = injectiveMoment H node2745 := by
  calc
    injectiveMoment H raw4189 = injectiveMoment H raw4189step0 := by
      have heq : raw4189step0 = (fun i j => raw4189 (permutation114 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4189 permutation114 permutation18
    _ = injectiveMoment H node2745 := by rfl

def raw4190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw4190step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical4190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4190 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw4190 = injectiveMoment H raw4190step0 := by
      have heq : raw4190step0 = (fun i j => raw4190 (permutation27 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4190 permutation27 permutation20
    _ = injectiveMoment H node1057 := by rfl

def raw4191 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4191step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -2, 0], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw4191step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical4191 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4191 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw4191 = injectiveMoment H raw4191step0 := by
      have heq : raw4191step0 = -raw4191 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4191).symm
    injectiveMoment H raw4191step0 = injectiveMoment H raw4191step1 := by
      have heq : raw4191step1 = (fun i j => raw4191step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4191step0 permutation29 permutation15
    _ = injectiveMoment H node1057 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
