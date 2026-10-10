import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9280 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def raw9280step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 2, -2, 2]]

def raw9280step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 2, -2, 2]]

def raw9280step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9280 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9280 = injectiveMoment H node1521 := by
  calc
    injectiveMoment H raw9280 = injectiveMoment H raw9280step0 := by
      have heq : raw9280step0 = -raw9280 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9280).symm
    injectiveMoment H raw9280step0 = injectiveMoment H raw9280step1 := by
      have hz : ∀ j, raw9280step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9280step1 = (fun i j => raw9280step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9280step0 permutation221 hz
    injectiveMoment H raw9280step1 = injectiveMoment H raw9280step2 := by
      have heq : raw9280step2 = (fun i j => raw9280step1 (permutation139 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9280step1 permutation139 permutation11
    _ = injectiveMoment H node1521 := by rfl

def raw9281 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9281step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9281step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9281 = injectiveMoment H node1749 := by
  calc
    injectiveMoment H raw9281 = injectiveMoment H raw9281step0 := by
      have hz : ∀ j, raw9281 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9281step0 = (fun i j => raw9281 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9281 permutation221 hz
    injectiveMoment H raw9281step0 = injectiveMoment H raw9281step1 := by
      have heq : raw9281step1 = (fun i j => raw9281step0 (permutation139 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9281step0 permutation139 permutation13
    _ = injectiveMoment H node1749 := by rfl

def raw9282 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9282step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9282step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9282 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9282 = injectiveMoment H node1752 := by
  calc
    injectiveMoment H raw9282 = injectiveMoment H raw9282step0 := by
      have hz : ∀ j, raw9282 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9282step0 = (fun i j => raw9282 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9282 permutation221 hz
    injectiveMoment H raw9282step0 = injectiveMoment H raw9282step1 := by
      have heq : raw9282step1 = (fun i j => raw9282step0 (permutation143 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9282step0 permutation143 permutation29
    _ = injectiveMoment H node1752 := by rfl

def raw9283 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9283step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9283step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9283 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9283 = injectiveMoment H node1524 := by
  calc
    injectiveMoment H raw9283 = injectiveMoment H raw9283step0 := by
      have hz : ∀ j, raw9283 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9283step0 = (fun i j => raw9283 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9283 permutation221 hz
    injectiveMoment H raw9283step0 = injectiveMoment H raw9283step1 := by
      have heq : raw9283step1 = (fun i j => raw9283step0 (permutation128 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9283step0 permutation128 permutation14
    _ = injectiveMoment H node1524 := by rfl

def raw9284 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9284step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9284step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9284 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9284 = injectiveMoment H node1823 := by
  calc
    injectiveMoment H raw9284 = injectiveMoment H raw9284step0 := by
      have hz : ∀ j, raw9284 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9284step0 = (fun i j => raw9284 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9284 permutation221 hz
    injectiveMoment H raw9284step0 = injectiveMoment H raw9284step1 := by
      have heq : raw9284step1 = (fun i j => raw9284step0 (permutation129 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9284step0 permutation129 permutation14
    _ = injectiveMoment H node1823 := by rfl

def raw9285 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def raw9285step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw9285step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw9285step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9285 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9285 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw9285 = injectiveMoment H raw9285step0 := by
      have heq : raw9285step0 = -raw9285 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9285).symm
    injectiveMoment H raw9285step0 = injectiveMoment H raw9285step1 := by
      have hz : ∀ j, raw9285step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9285step1 = (fun i j => raw9285step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9285step0 permutation221 hz
    injectiveMoment H raw9285step1 = injectiveMoment H raw9285step2 := by
      have heq : raw9285step2 = (fun i j => raw9285step1 (permutation145 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9285step1 permutation145 permutation18
    _ = injectiveMoment H node2448 := by rfl

def raw9286 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def raw9286step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw9286step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw9286step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

theorem canonical9286 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9286 = injectiveMoment H node2831 := by
  calc
    injectiveMoment H raw9286 = injectiveMoment H raw9286step0 := by
      have heq : raw9286step0 = -raw9286 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9286).symm
    injectiveMoment H raw9286step0 = injectiveMoment H raw9286step1 := by
      have hz : ∀ j, raw9286step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9286step1 = (fun i j => raw9286step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9286step0 permutation221 hz
    injectiveMoment H raw9286step1 = injectiveMoment H raw9286step2 := by
      have heq : raw9286step2 = (fun i j => raw9286step1 (permutation116 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9286step1 permutation116 permutation17
    _ = injectiveMoment H node2831 := by rfl

def raw9287 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw9287step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw9287step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw9287step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

theorem canonical9287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9287 = injectiveMoment H node2407 := by
  calc
    injectiveMoment H raw9287 = injectiveMoment H raw9287step0 := by
      have heq : raw9287step0 = -raw9287 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9287).symm
    injectiveMoment H raw9287step0 = injectiveMoment H raw9287step1 := by
      have hz : ∀ j, raw9287step0 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw9287step1 = (fun i j => raw9287step0 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9287step0 permutation241 hz
    injectiveMoment H raw9287step1 = injectiveMoment H raw9287step2 := by
      have heq : raw9287step2 = (fun i j => raw9287step1 (permutation139 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9287step1 permutation139 permutation15
    _ = injectiveMoment H node2407 := by rfl

def raw9288 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def raw9288step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw9288step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw9288step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical9288 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9288 = injectiveMoment H node2830 := by
  calc
    injectiveMoment H raw9288 = injectiveMoment H raw9288step0 := by
      have heq : raw9288step0 = -raw9288 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9288).symm
    injectiveMoment H raw9288step0 = injectiveMoment H raw9288step1 := by
      have hz : ∀ j, raw9288step0 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw9288step1 = (fun i j => raw9288step0 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9288step0 permutation241 hz
    injectiveMoment H raw9288step1 = injectiveMoment H raw9288step2 := by
      have heq : raw9288step2 = (fun i j => raw9288step1 (permutation116 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9288step1 permutation116 permutation17
    _ = injectiveMoment H node2830 := by rfl

def raw9289 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9289step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9289step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical9289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9289 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw9289 = injectiveMoment H raw9289step0 := by
      have hz : ∀ j, raw9289 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw9289step0 = (fun i j => raw9289 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9289 permutation241 hz
    injectiveMoment H raw9289step0 = injectiveMoment H raw9289step1 := by
      have heq : raw9289step1 = (fun i j => raw9289step0 (permutation139 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9289step0 permutation139 permutation20
    _ = injectiveMoment H node1746 := by rfl

def raw9290 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, -1, 1], ![2, -2, 1, -1]]

def raw9290step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

theorem canonical9290 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9290 = injectiveMoment H node3317 := by
  calc
    injectiveMoment H raw9290 = injectiveMoment H raw9290step0 := by
      have heq : raw9290step0 = (fun i j => raw9290 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9290 permutation258 permutation9
    _ = injectiveMoment H node3317 := by rfl

def raw9291 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 0, 0]]

def raw9291step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical9291 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9291 = injectiveMoment H node3165 := by
  calc
    injectiveMoment H raw9291 = injectiveMoment H raw9291step0 := by
      have heq : raw9291step0 = (fun i j => raw9291 (permutation258 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9291 permutation258 permutation12
    _ = injectiveMoment H node3165 := by rfl

def raw9292 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def raw9292step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical9292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9292 = injectiveMoment H node3288 := by
  calc
    injectiveMoment H raw9292 = injectiveMoment H raw9292step0 := by
      have heq : raw9292step0 = (fun i j => raw9292 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9292 permutation258 permutation9
    _ = injectiveMoment H node3288 := by rfl

def raw9293 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9293step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9293 = injectiveMoment H node3030 := by
  calc
    injectiveMoment H raw9293 = injectiveMoment H raw9293step0 := by
      have heq : raw9293step0 = (fun i j => raw9293 (permutation363 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9293 permutation363 permutation13
    _ = injectiveMoment H node3030 := by rfl

def raw9294 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -2, 1, 3], ![2, 1, 0, -3]]

def raw9294step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

theorem canonical9294 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9294 = injectiveMoment H node2883 := by
  calc
    injectiveMoment H raw9294 = injectiveMoment H raw9294step0 := by
      have heq : raw9294step0 = (fun i j => raw9294 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9294 permutation258 permutation9
    _ = injectiveMoment H node2883 := by rfl

def raw9295 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 0, 0, -2]]

def raw9295step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical9295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9295 = injectiveMoment H node3338 := by
  calc
    injectiveMoment H raw9295 = injectiveMoment H raw9295step0 := by
      have heq : raw9295step0 = (fun i j => raw9295 (permutation259 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9295 permutation259 permutation15
    _ = injectiveMoment H node3338 := by rfl

def raw9296 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -1, 1, -2]]

def raw9296step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 1, -1, 2]]

def raw9296step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical9296 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9296 = injectiveMoment H node3445 := by
  calc
    injectiveMoment H raw9296 = injectiveMoment H raw9296step0 := by
      have heq : raw9296step0 = -raw9296 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9296).symm
    injectiveMoment H raw9296step0 = injectiveMoment H raw9296step1 := by
      have heq : raw9296step1 = (fun i j => raw9296step0 (permutation247 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9296step0 permutation247 permutation17
    _ = injectiveMoment H node3445 := by rfl

def raw9297 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, -1, 2], ![2, -2, 2, -2]]

def raw9297step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical9297 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9297 = injectiveMoment H node3255 := by
  calc
    injectiveMoment H raw9297 = injectiveMoment H raw9297step0 := by
      have heq : raw9297step0 = (fun i j => raw9297 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9297 permutation258 permutation9
    _ = injectiveMoment H node3255 := by rfl

def raw9298 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 1, -1]]

def raw9298step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 2, -1, 1]]

def raw9298step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9298 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9298 = injectiveMoment H node3092 := by
  calc
    injectiveMoment H raw9298 = injectiveMoment H raw9298step0 := by
      have heq : raw9298step0 = -raw9298 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9298).symm
    injectiveMoment H raw9298step0 = injectiveMoment H raw9298step1 := by
      have heq : raw9298step1 = (fun i j => raw9298step0 (permutation363 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9298step0 permutation363 permutation11
    _ = injectiveMoment H node3092 := by rfl

def raw9299 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 1, 2, -1]]

def raw9299step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical9299 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9299 = injectiveMoment H node3257 := by
  calc
    injectiveMoment H raw9299 = injectiveMoment H raw9299step0 := by
      have heq : raw9299step0 = (fun i j => raw9299 (permutation355 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9299 permutation355 permutation10
    _ = injectiveMoment H node3257 := by rfl

def raw9300 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 1, 0]]

def raw9300step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-2, 2, 0, 0], ![2, -1, -1, 0]]

def raw9300step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9300 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9300 = injectiveMoment H node3166 := by
  calc
    injectiveMoment H raw9300 = injectiveMoment H raw9300step0 := by
      have heq : raw9300step0 = -raw9300 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9300).symm
    injectiveMoment H raw9300step0 = injectiveMoment H raw9300step1 := by
      have heq : raw9300step1 = (fun i j => raw9300step0 (permutation258 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9300step0 permutation258 permutation14
    _ = injectiveMoment H node3166 := by rfl

def raw9301 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def raw9301step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![-1, 0, 0, 1], ![2, -2, -1, 1]]

def raw9301step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9301 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9301 = injectiveMoment H node3092 := by
  calc
    injectiveMoment H raw9301 = injectiveMoment H raw9301step0 := by
      have heq : raw9301step0 = -raw9301 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9301).symm
    injectiveMoment H raw9301step0 = injectiveMoment H raw9301step1 := by
      have heq : raw9301step1 = (fun i j => raw9301step0 (permutation368 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9301step0 permutation368 permutation17
    _ = injectiveMoment H node3092 := by rfl

def raw9302 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9302step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem canonical9302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9302 = injectiveMoment H node3329 := by
  calc
    injectiveMoment H raw9302 = injectiveMoment H raw9302step0 := by
      have heq : raw9302step0 = (fun i j => raw9302 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9302 permutation258 permutation9
    _ = injectiveMoment H node3329 := by rfl

def raw9303 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9303step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9303 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9303 = injectiveMoment H node3312 := by
  calc
    injectiveMoment H raw9303 = injectiveMoment H raw9303step0 := by
      have heq : raw9303step0 = (fun i j => raw9303 (permutation356 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9303 permutation356 permutation10
    _ = injectiveMoment H node3312 := by rfl

def raw9304 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9304step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical9304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9304 = injectiveMoment H node3321 := by
  calc
    injectiveMoment H raw9304 = injectiveMoment H raw9304step0 := by
      have heq : raw9304step0 = (fun i j => raw9304 (permutation356 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9304 permutation356 permutation10
    _ = injectiveMoment H node3321 := by rfl

def raw9305 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, -1, 1], ![1, -1, 2, -2]]

def raw9305step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical9305 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9305 = injectiveMoment H node3319 := by
  calc
    injectiveMoment H raw9305 = injectiveMoment H raw9305step0 := by
      have heq : raw9305step0 = (fun i j => raw9305 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9305 permutation258 permutation9
    _ = injectiveMoment H node3319 := by rfl

def raw9306 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 1, -1]]

def raw9306step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9306 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9306 = injectiveMoment H node3167 := by
  calc
    injectiveMoment H raw9306 = injectiveMoment H raw9306step0 := by
      have heq : raw9306step0 = (fun i j => raw9306 (permutation258 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9306 permutation258 permutation12
    _ = injectiveMoment H node3167 := by rfl

def raw9307 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 2, 2, -2]]

def raw9307step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9307 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9307 = injectiveMoment H node3312 := by
  calc
    injectiveMoment H raw9307 = injectiveMoment H raw9307step0 := by
      have heq : raw9307step0 = (fun i j => raw9307 (permutation355 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9307 permutation355 permutation10
    _ = injectiveMoment H node3312 := by rfl

def raw9308 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 1, -1]]

def raw9308step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9308 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9308 = injectiveMoment H node3043 := by
  calc
    injectiveMoment H raw9308 = injectiveMoment H raw9308step0 := by
      have heq : raw9308step0 = (fun i j => raw9308 (permutation355 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9308 permutation355 permutation14
    _ = injectiveMoment H node3043 := by rfl

def raw9309 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 0, 0]]

def raw9309step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9309 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9309 = injectiveMoment H node3167 := by
  calc
    injectiveMoment H raw9309 = injectiveMoment H raw9309step0 := by
      have heq : raw9309step0 = (fun i j => raw9309 (permutation308 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9309 permutation308 permutation12
    _ = injectiveMoment H node3167 := by rfl

def raw9310 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw9310step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -1, 0]]

def raw9310step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9310 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9310 = injectiveMoment H node3393 := by
  calc
    injectiveMoment H raw9310 = injectiveMoment H raw9310step0 := by
      have heq : raw9310step0 = -raw9310 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9310).symm
    injectiveMoment H raw9310step0 = injectiveMoment H raw9310step1 := by
      have heq : raw9310step1 = (fun i j => raw9310step0 (permutation368 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9310step0 permutation368 permutation18
    _ = injectiveMoment H node3393 := by rfl

def raw9311 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, -2, 1, 0]]

def raw9311step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem canonical9311 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9311 = injectiveMoment H node2450 := by
  calc
    injectiveMoment H raw9311 = injectiveMoment H raw9311step0 := by
      have heq : raw9311step0 = (fun i j => raw9311 (permutation116 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9311 permutation116 permutation13
    _ = injectiveMoment H node2450 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
