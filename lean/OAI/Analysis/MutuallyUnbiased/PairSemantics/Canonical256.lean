import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8192 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0]]

def raw8192step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8192 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw8192 = injectiveMoment H raw8192step0 := by
      have heq : raw8192step0 = (fun i j => raw8192 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8192 permutation23 permutation4
    _ = injectiveMoment H node284 := by rfl

def raw8193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2], ![-3, 0, 3]]

def raw8193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical8193 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8193 = injectiveMoment H node1401 := by
  calc
    injectiveMoment H raw8193 = injectiveMoment H raw8193step0 := by
      have heq : raw8193step0 = -raw8193 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8193).symm
    injectiveMoment H raw8193step0 = injectiveMoment H raw8193step1 := by
      have heq : raw8193step1 = (fun i j => raw8193step0 (permutation338 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8193step0 permutation338 permutation3
    _ = injectiveMoment H node1401 := by rfl

def raw8194 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw8194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0]]

def raw8194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8194 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8194 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H raw8194 = injectiveMoment H raw8194step0 := by
      have heq : raw8194step0 = -raw8194 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8194).symm
    injectiveMoment H raw8194step0 = injectiveMoment H raw8194step1 := by
      have heq : raw8194step1 = (fun i j => raw8194step0 (permutation128 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8194step0 permutation128 permutation4
    _ = injectiveMoment H node1291 := by rfl

def raw8195 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0]]

def raw8195step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1]]

def raw8195step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical8195 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8195 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8195 = injectiveMoment H raw8195step0 := by
      have hz : ∀ j, raw8195 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8195step0 = (fun i j => raw8195 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8195 permutation27 hz
    injectiveMoment H raw8195step0 = injectiveMoment H raw8195step1 := by
      have hz : ∀ i, raw8195step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8195step1 = (fun i j => raw8195step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8195step0 permutation3 hz
    _ = injectiveMoment H node11 := by rfl

def raw8196 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1]]

def raw8196step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw8196step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8196 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw8196 = injectiveMoment H raw8196step0 := by
      have hz : ∀ i, raw8196 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8196step0 = (fun i j => raw8196 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8196 permutation3 hz
    injectiveMoment H raw8196step0 = injectiveMoment H raw8196step1 := by
      have heq : raw8196step1 = (fun i j => raw8196step0 (permutation51 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8196step0 permutation51 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw8197 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def raw8197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical8197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8197 = injectiveMoment H node1392 := by
  calc
    injectiveMoment H raw8197 = injectiveMoment H raw8197step0 := by
      have heq : raw8197step0 = (fun i j => raw8197 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8197 permutation258 permutation3
    _ = injectiveMoment H node1392 := by rfl

def raw8198 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8198 = injectiveMoment H node1870 := by
  calc
    injectiveMoment H raw8198 = injectiveMoment H raw8198step0 := by
      have heq : raw8198step0 = (fun i j => raw8198 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8198 permutation258 permutation3
    _ = injectiveMoment H node1870 := by rfl

def raw8199 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8199 = injectiveMoment H node2301 := by
  calc
    injectiveMoment H raw8199 = injectiveMoment H raw8199step0 := by
      have heq : raw8199step0 = (fun i j => raw8199 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8199 permutation308 permutation3
    _ = injectiveMoment H node2301 := by rfl

def raw8200 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def raw8200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem canonical8200 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8200 = injectiveMoment H node1417 := by
  calc
    injectiveMoment H raw8200 = injectiveMoment H raw8200step0 := by
      have heq : raw8200step0 = (fun i j => raw8200 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8200 permutation308 permutation3
    _ = injectiveMoment H node1417 := by rfl

def raw8201 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8201 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8201 = injectiveMoment H node2120 := by
  calc
    injectiveMoment H raw8201 = injectiveMoment H raw8201step0 := by
      have heq : raw8201step0 = (fun i j => raw8201 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8201 permutation308 permutation3
    _ = injectiveMoment H node2120 := by rfl

def raw8202 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8202 = injectiveMoment H node1871 := by
  calc
    injectiveMoment H raw8202 = injectiveMoment H raw8202step0 := by
      have heq : raw8202step0 = (fun i j => raw8202 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8202 permutation308 permutation3
    _ = injectiveMoment H node1871 := by rfl

def raw8203 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def raw8203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical8203 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8203 = injectiveMoment H node1418 := by
  calc
    injectiveMoment H raw8203 = injectiveMoment H raw8203step0 := by
      have heq : raw8203step0 = (fun i j => raw8203 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8203 permutation308 permutation3
    _ = injectiveMoment H node1418 := by rfl

def raw8204 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1]]

def raw8204step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw8204step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8204 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8204 = injectiveMoment H raw8204step0 := by
      have hz : ∀ i, raw8204 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8204step0 = (fun i j => raw8204 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8204 permutation3 hz
    injectiveMoment H raw8204step0 = injectiveMoment H raw8204step1 := by
      have heq : raw8204step1 = (fun i j => raw8204step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8204step0 permutation13 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8205 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8205 = injectiveMoment H node2122 := by
  calc
    injectiveMoment H raw8205 = injectiveMoment H raw8205step0 := by
      have heq : raw8205step0 = (fun i j => raw8205 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8205 permutation262 permutation3
    _ = injectiveMoment H node2122 := by rfl

def raw8206 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8206 = injectiveMoment H node1395 := by
  calc
    injectiveMoment H raw8206 = injectiveMoment H raw8206step0 := by
      have heq : raw8206step0 = (fun i j => raw8206 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8206 permutation258 permutation3
    _ = injectiveMoment H node1395 := by rfl

def raw8207 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8207 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8207 = injectiveMoment H node1872 := by
  calc
    injectiveMoment H raw8207 = injectiveMoment H raw8207step0 := by
      have heq : raw8207step0 = (fun i j => raw8207 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8207 permutation262 permutation3
    _ = injectiveMoment H node1872 := by rfl

def raw8208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8208 = injectiveMoment H node2472 := by
  calc
    injectiveMoment H raw8208 = injectiveMoment H raw8208step0 := by
      have heq : raw8208step0 = (fun i j => raw8208 (permutation399 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8208 permutation399 permutation4
    _ = injectiveMoment H node2472 := by rfl

def raw8209 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8209 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8209 = injectiveMoment H node1432 := by
  calc
    injectiveMoment H raw8209 = injectiveMoment H raw8209step0 := by
      have heq : raw8209step0 = (fun i j => raw8209 (permutation334 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8209 permutation334 permutation4
    _ = injectiveMoment H node1432 := by rfl

def raw8210 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8210 = injectiveMoment H node1419 := by
  calc
    injectiveMoment H raw8210 = injectiveMoment H raw8210step0 := by
      have heq : raw8210step0 = (fun i j => raw8210 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8210 permutation308 permutation3
    _ = injectiveMoment H node1419 := by rfl

def raw8211 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def raw8211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical8211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8211 = injectiveMoment H node2101 := by
  calc
    injectiveMoment H raw8211 = injectiveMoment H raw8211step0 := by
      have heq : raw8211step0 = (fun i j => raw8211 (permutation248 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8211 permutation248 permutation3
    _ = injectiveMoment H node2101 := by rfl

def raw8212 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def raw8212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical8212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8212 = injectiveMoment H node2091 := by
  calc
    injectiveMoment H raw8212 = injectiveMoment H raw8212step0 := by
      have heq : raw8212step0 = (fun i j => raw8212 (permutation190 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8212 permutation190 permutation5
    _ = injectiveMoment H node2091 := by rfl

def raw8213 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def raw8213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

theorem canonical8213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8213 = injectiveMoment H node1864 := by
  calc
    injectiveMoment H raw8213 = injectiveMoment H raw8213step0 := by
      have heq : raw8213step0 = (fun i j => raw8213 (permutation373 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8213 permutation373 permutation3
    _ = injectiveMoment H node1864 := by rfl

def raw8214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8214 = injectiveMoment H node2473 := by
  calc
    injectiveMoment H raw8214 = injectiveMoment H raw8214step0 := by
      have heq : raw8214step0 = (fun i j => raw8214 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8214 permutation294 permutation3
    _ = injectiveMoment H node2473 := by rfl

def raw8215 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2]]

def raw8215step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8216 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![0, 0, 0]]

def raw8216step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2]]

def raw8216step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8216 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8216 = injectiveMoment H raw8216step0 := by
      have hz : ∀ j, raw8216 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw8216step0 = (fun i j => raw8216 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8216 permutation7 hz
    injectiveMoment H raw8216step0 = injectiveMoment H raw8216step1 := by
      have hz : ∀ i, raw8216step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8216step1 = (fun i j => raw8216step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8216step0 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8217 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![0, -1, 1]]

def raw8217step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![3, -3], ![-1, 1]]

def raw8217step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8217 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8217 = injectiveMoment H raw8217step0 := by
      have hz : ∀ i, raw8217 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8217step0 = (fun i j => raw8217 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8217 permutation3 hz
    injectiveMoment H raw8217step0 = injectiveMoment H raw8217step1 := by
      have heq : raw8217step1 = (fun i j => raw8217step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8217step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw8218 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def raw8218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8218 = injectiveMoment H node2107 := by
  calc
    injectiveMoment H raw8218 = injectiveMoment H raw8218step0 := by
      have heq : raw8218step0 = (fun i j => raw8218 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8218 permutation294 permutation3
    _ = injectiveMoment H node2107 := by rfl

def raw8219 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def raw8219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical8219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8219 = injectiveMoment H node2099 := by
  calc
    injectiveMoment H raw8219 = injectiveMoment H raw8219step0 := by
      have heq : raw8219step0 = (fun i j => raw8219 (permutation151 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8219 permutation151 permutation5
    _ = injectiveMoment H node2099 := by rfl

def raw8220 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def raw8220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8220 = injectiveMoment H node1534 := by
  calc
    injectiveMoment H raw8220 = injectiveMoment H raw8220step0 := by
      have heq : raw8220step0 = (fun i j => raw8220 (permutation397 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8220 permutation397 permutation4
    _ = injectiveMoment H node1534 := by rfl

def raw8221 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 1, 0, 3], ![4, 1, -2, -3]]

def raw8221step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 1, 1], ![2, 0, -2], ![0, 3, -3]]

def raw8221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![-2, 0, 2], ![0, -3, 3]]

def raw8221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

theorem canonical8221 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8221 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw8221 = injectiveMoment H raw8221step0 := by
      have heq : raw8221step0 = raw8221.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8221).symm
    injectiveMoment H raw8221step0 = injectiveMoment H raw8221step1 := by
      have heq : raw8221step1 = -raw8221step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8221step0).symm
    injectiveMoment H raw8221step1 = injectiveMoment H raw8221step2 := by
      have heq : raw8221step2 = (fun i j => raw8221step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8221step1 permutation25 permutation3
    _ = injectiveMoment H node193 := by rfl

def raw8222 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 2, -1, 3], ![4, 0, -1, -3]]

def raw8222step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 2, 0], ![2, -1, -1], ![0, 3, -3]]

def raw8222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

theorem canonical8222 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8222 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw8222 = injectiveMoment H raw8222step0 := by
      have heq : raw8222step0 = raw8222.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8222).symm
    injectiveMoment H raw8222step0 = injectiveMoment H raw8222step1 := by
      have heq : raw8222step1 = (fun i j => raw8222step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8222step0 permutation19 permutation4
    _ = injectiveMoment H node193 := by rfl

def raw8223 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 2, 0, 2], ![4, 0, -2, -2]]

def raw8223step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 2, 0], ![2, 0, -2], ![0, 2, -2]]

def raw8223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

theorem canonical8223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8223 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw8223 = injectiveMoment H raw8223step0 := by
      have heq : raw8223step0 = raw8223.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8223).symm
    injectiveMoment H raw8223step0 = injectiveMoment H raw8223step1 := by
      have heq : raw8223step1 = (fun i j => raw8223step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8223step0 permutation19 permutation4
    _ = injectiveMoment H node199 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
