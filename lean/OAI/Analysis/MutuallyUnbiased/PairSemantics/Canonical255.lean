import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8160 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8160step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8160 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8160 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw8160 = injectiveMoment H raw8160step0 := by
      have heq : raw8160step0 = (fun i j => raw8160 (permutation15 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8160 permutation15 permutation3
    _ = injectiveMoment H node279 := by rfl

def raw8161 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1]]

def raw8161step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical8161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8161 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw8161 = injectiveMoment H raw8161step0 := by
      have heq : raw8161step0 = (fun i j => raw8161 (permutation15 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8161 permutation15 permutation3
    _ = injectiveMoment H node280 := by rfl

def raw8162 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0]]

def raw8162step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical8162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8162 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw8162 = injectiveMoment H raw8162step0 := by
      have heq : raw8162step0 = (fun i j => raw8162 (permutation15 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8162 permutation15 permutation3
    _ = injectiveMoment H node281 := by rfl

def raw8163 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0]]

def raw8163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8163 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8163 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H raw8163 = injectiveMoment H raw8163step0 := by
      have heq : raw8163step0 = -raw8163 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8163).symm
    injectiveMoment H raw8163step0 = injectiveMoment H raw8163step1 := by
      have heq : raw8163step1 = (fun i j => raw8163step0 (permutation131 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8163step0 permutation131 permutation4
    _ = injectiveMoment H node1291 := by rfl

def raw8164 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw8164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8164 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw8164 = injectiveMoment H raw8164step0 := by
      have heq : raw8164step0 = (fun i j => raw8164 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8164 permutation17 permutation4
    _ = injectiveMoment H node294 := by rfl

def raw8165 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0]]

def raw8165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8165 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw8165 = injectiveMoment H raw8165step0 := by
      have heq : raw8165step0 = (fun i j => raw8165 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8165 permutation17 permutation4
    _ = injectiveMoment H node291 := by rfl

def raw8166 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1]]

def raw8166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8166 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8166 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw8166 = injectiveMoment H raw8166step0 := by
      have heq : raw8166step0 = (fun i j => raw8166 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8166 permutation17 permutation4
    _ = injectiveMoment H node279 := by rfl

def raw8167 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![1, 0, -1]]

def raw8167step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8167 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8167 = injectiveMoment H raw8167step0 := by
      have heq : raw8167step0 = (fun i j => raw8167 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8167 permutation5 permutation4
    _ = injectiveMoment H node62 := by rfl

def raw8168 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 1, -2]]

def raw8168step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

theorem canonical8168 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8168 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw8168 = injectiveMoment H raw8168step0 := by
      have heq : raw8168step0 = (fun i j => raw8168 (permutation15 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8168 permutation15 permutation4
    _ = injectiveMoment H node274 := by rfl

def raw8169 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![1, -1, 0]]

def raw8169step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8169 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw8169 = injectiveMoment H raw8169step0 := by
      have heq : raw8169step0 = (fun i j => raw8169 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8169 permutation5 permutation4
    _ = injectiveMoment H node57 := by rfl

def raw8170 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1]]

def raw8170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8170 = injectiveMoment H node256 := by
  calc
    injectiveMoment H raw8170 = injectiveMoment H raw8170step0 := by
      have heq : raw8170step0 = (fun i j => raw8170 (permutation15 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8170 permutation15 permutation4
    _ = injectiveMoment H node256 := by rfl

def raw8171 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![0, 4, -4]]

def raw8171step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![4, -4]]

def raw8171step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

theorem canonical8171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8171 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw8171 = injectiveMoment H raw8171step0 := by
      have hz : ∀ i, raw8171 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8171step0 = (fun i j => raw8171 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8171 permutation3 hz
    injectiveMoment H raw8171step0 = injectiveMoment H raw8171step1 := by
      have heq : raw8171step1 = (fun i j => raw8171step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8171step0 permutation7 permutation2
    _ = injectiveMoment H node9 := by rfl

def raw8172 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0]]

def raw8172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8172 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw8172 = injectiveMoment H raw8172step0 := by
      have heq : raw8172step0 = (fun i j => raw8172 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8172 permutation23 permutation4
    _ = injectiveMoment H node254 := by rfl

def raw8173 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def raw8173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![-2, -1, 3]]

def raw8173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical8173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8173 = injectiveMoment H node1881 := by
  calc
    injectiveMoment H raw8173 = injectiveMoment H raw8173step0 := by
      have heq : raw8173step0 = -raw8173 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8173).symm
    injectiveMoment H raw8173step0 = injectiveMoment H raw8173step1 := by
      have heq : raw8173step1 = (fun i j => raw8173step0 (permutation379 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8173step0 permutation379 permutation3
    _ = injectiveMoment H node1881 := by rfl

def raw8174 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def raw8174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8174 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8174 = injectiveMoment H node1543 := by
  calc
    injectiveMoment H raw8174 = injectiveMoment H raw8174step0 := by
      have heq : raw8174step0 = (fun i j => raw8174 (permutation337 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8174 permutation337 permutation4
    _ = injectiveMoment H node1543 := by rfl

def raw8175 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2], ![-3, 0, 3]]

def raw8175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

theorem canonical8175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8175 = injectiveMoment H node1398 := by
  calc
    injectiveMoment H raw8175 = injectiveMoment H raw8175step0 := by
      have heq : raw8175step0 = -raw8175 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8175).symm
    injectiveMoment H raw8175step0 = injectiveMoment H raw8175step1 := by
      have heq : raw8175step1 = (fun i j => raw8175step0 (permutation364 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8175step0 permutation364 permutation3
    _ = injectiveMoment H node1398 := by rfl

def raw8176 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def raw8176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8176 = injectiveMoment H node1874 := by
  calc
    injectiveMoment H raw8176 = injectiveMoment H raw8176step0 := by
      have heq : raw8176step0 = -raw8176 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8176).symm
    injectiveMoment H raw8176step0 = injectiveMoment H raw8176step1 := by
      have heq : raw8176step1 = (fun i j => raw8176step0 (permutation364 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8176step0 permutation364 permutation3
    _ = injectiveMoment H node1874 := by rfl

def raw8177 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def raw8177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8177 = injectiveMoment H node2126 := by
  calc
    injectiveMoment H raw8177 = injectiveMoment H raw8177step0 := by
      have heq : raw8177step0 = -raw8177 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8177).symm
    injectiveMoment H raw8177step0 = injectiveMoment H raw8177step1 := by
      have heq : raw8177step1 = (fun i j => raw8177step0 (permutation364 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8177step0 permutation364 permutation3
    _ = injectiveMoment H node2126 := by rfl

def raw8178 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8178 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8178 = injectiveMoment H node2113 := by
  calc
    injectiveMoment H raw8178 = injectiveMoment H raw8178step0 := by
      have heq : raw8178step0 = (fun i j => raw8178 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8178 permutation258 permutation3
    _ = injectiveMoment H node2113 := by rfl

def raw8179 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def raw8179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

theorem canonical8179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8179 = injectiveMoment H node1414 := by
  calc
    injectiveMoment H raw8179 = injectiveMoment H raw8179step0 := by
      have heq : raw8179step0 = (fun i j => raw8179 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8179 permutation258 permutation3
    _ = injectiveMoment H node1414 := by rfl

def raw8180 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def raw8180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8180 = injectiveMoment H node2114 := by
  calc
    injectiveMoment H raw8180 = injectiveMoment H raw8180step0 := by
      have heq : raw8180step0 = (fun i j => raw8180 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8180 permutation258 permutation3
    _ = injectiveMoment H node2114 := by rfl

def raw8181 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8181 = injectiveMoment H node2139 := by
  calc
    injectiveMoment H raw8181 = injectiveMoment H raw8181step0 := by
      have heq : raw8181step0 = (fun i j => raw8181 (permutation357 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8181 permutation357 permutation4
    _ = injectiveMoment H node2139 := by rfl

def raw8182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def raw8182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

theorem canonical8182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8182 = injectiveMoment H node1435 := by
  calc
    injectiveMoment H raw8182 = injectiveMoment H raw8182step0 := by
      have heq : raw8182step0 = (fun i j => raw8182 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8182 permutation308 permutation3
    _ = injectiveMoment H node1435 := by rfl

def raw8183 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![0, -1, 1]]

def raw8183step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![4, -4], ![-1, 1]]

def raw8183step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical8183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8183 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw8183 = injectiveMoment H raw8183step0 := by
      have hz : ∀ i, raw8183 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8183step0 = (fun i j => raw8183 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8183 permutation3 hz
    injectiveMoment H raw8183step0 = injectiveMoment H raw8183step1 := by
      have heq : raw8183step1 = (fun i j => raw8183step0 (permutation24 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8183step0 permutation24 permutation2
    _ = injectiveMoment H node16 := by rfl

def raw8184 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def raw8184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8184 = injectiveMoment H node2117 := by
  calc
    injectiveMoment H raw8184 = injectiveMoment H raw8184step0 := by
      have heq : raw8184step0 = (fun i j => raw8184 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8184 permutation262 permutation3
    _ = injectiveMoment H node2117 := by rfl

def raw8185 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def raw8185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8185 = injectiveMoment H node2298 := by
  calc
    injectiveMoment H raw8185 = injectiveMoment H raw8185step0 := by
      have heq : raw8185step0 = (fun i j => raw8185 (permutation299 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8185 permutation299 permutation4
    _ = injectiveMoment H node2298 := by rfl

def raw8186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def raw8186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8186 = injectiveMoment H node1416 := by
  calc
    injectiveMoment H raw8186 = injectiveMoment H raw8186step0 := by
      have heq : raw8186step0 = (fun i j => raw8186 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8186 permutation258 permutation3
    _ = injectiveMoment H node1416 := by rfl

def raw8187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def raw8187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8187 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8187 = injectiveMoment H node2116 := by
  calc
    injectiveMoment H raw8187 = injectiveMoment H raw8187step0 := by
      have heq : raw8187step0 = (fun i j => raw8187 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8187 permutation262 permutation3
    _ = injectiveMoment H node2116 := by rfl

def raw8188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def raw8188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8188 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8188 = injectiveMoment H node2672 := by
  calc
    injectiveMoment H raw8188 = injectiveMoment H raw8188step0 := by
      have heq : raw8188step0 = (fun i j => raw8188 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8188 permutation294 permutation3
    _ = injectiveMoment H node2672 := by rfl

def raw8189 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def raw8189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]

def raw8189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

theorem canonical8189 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8189 = injectiveMoment H node1410 := by
  calc
    injectiveMoment H raw8189 = injectiveMoment H raw8189step0 := by
      have heq : raw8189step0 = -raw8189 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8189).symm
    injectiveMoment H raw8189step0 = injectiveMoment H raw8189step1 := by
      have heq : raw8189step1 = (fun i j => raw8189step0 (permutation367 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8189step0 permutation367 permutation6
    _ = injectiveMoment H node1410 := by rfl

def raw8190 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0]]

def raw8190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0]]

def raw8190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8190 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8190 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H raw8190 = injectiveMoment H raw8190step0 := by
      have heq : raw8190step0 = -raw8190 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8190).symm
    injectiveMoment H raw8190step0 = injectiveMoment H raw8190step1 := by
      have heq : raw8190step1 = (fun i j => raw8190step0 (permutation129 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8190step0 permutation129 permutation4
    _ = injectiveMoment H node1291 := by rfl

def raw8191 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1]]

def raw8191step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8191 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw8191 = injectiveMoment H raw8191step0 := by
      have heq : raw8191step0 = (fun i j => raw8191 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8191 permutation23 permutation4
    _ = injectiveMoment H node294 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
