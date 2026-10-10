import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5280 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5280step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-2, 0, 2, 0, 0], ![2, 0, -2, 0, 0]]

def raw5280step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0], ![2, -2, 0, 0]]

def raw5280step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical5280 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5280 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw5280 = injectiveMoment H raw5280step0 := by
      have heq : raw5280step0 = raw5280.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5280).symm
    injectiveMoment H raw5280step0 = injectiveMoment H raw5280step1 := by
      have hz : ∀ i, raw5280step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw5280step1 = (fun i j => raw5280step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5280step0 permutation57 hz
    injectiveMoment H raw5280step1 = injectiveMoment H raw5280step2 := by
      have heq : raw5280step2 = (fun i j => raw5280step1 (permutation20 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5280step1 permutation20 permutation26
    _ = injectiveMoment H node1027 := by rfl

def raw5281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 0, 2, 0], ![2, 0, -2, 0]]

def raw5281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2], ![-2, 2, 0], ![2, -2, 0]]

def raw5281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical5281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5281 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw5281 = injectiveMoment H raw5281step0 := by
      have heq : raw5281step0 = raw5281.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5281).symm
    injectiveMoment H raw5281step0 = injectiveMoment H raw5281step1 := by
      have hz : ∀ i, raw5281step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5281step1 = (fun i j => raw5281step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5281step0 permutation15 hz
    injectiveMoment H raw5281step1 = injectiveMoment H raw5281step2 := by
      have heq : raw5281step2 = (fun i j => raw5281step1 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5281step1 permutation29 permutation6
    _ = injectiveMoment H node197 := by rfl

def raw5282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 0, 0, 2], ![2, 0, 0, -2]]

def raw5282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1], ![-2, 0, 2], ![2, 0, -2]]

def raw5282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5282 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5282 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw5282 = injectiveMoment H raw5282step0 := by
      have heq : raw5282step0 = raw5282.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5282).symm
    injectiveMoment H raw5282step0 = injectiveMoment H raw5282step1 := by
      have hz : ∀ i, raw5282step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5282step1 = (fun i j => raw5282step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5282step0 permutation15 hz
    injectiveMoment H raw5282step1 = injectiveMoment H raw5282step2 := by
      have heq : raw5282step2 = (fun i j => raw5282step1 (permutation20 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5282step1 permutation20 permutation6
    _ = injectiveMoment H node279 := by rfl

def raw5283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 0, 1, 1], ![2, 0, -1, -1]]

def raw5283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1], ![-2, 1, 1], ![2, -1, -1]]

def raw5283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5283 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5283 = injectiveMoment H node275 := by
  calc
    injectiveMoment H raw5283 = injectiveMoment H raw5283step0 := by
      have heq : raw5283step0 = raw5283.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5283).symm
    injectiveMoment H raw5283step0 = injectiveMoment H raw5283step1 := by
      have hz : ∀ i, raw5283step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5283step1 = (fun i j => raw5283step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5283step0 permutation15 hz
    injectiveMoment H raw5283step1 = injectiveMoment H raw5283step2 := by
      have heq : raw5283step2 = (fun i j => raw5283step1 (permutation19 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5283step1 permutation19 permutation6
    _ = injectiveMoment H node275 := by rfl

def raw5284 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5284step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-2, 1, 0, 0, 1], ![2, -1, 0, 0, -1]]

def raw5284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw5284step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical5284 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5284 = injectiveMoment H node1237 := by
  calc
    injectiveMoment H raw5284 = injectiveMoment H raw5284step0 := by
      have heq : raw5284step0 = raw5284.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5284).symm
    injectiveMoment H raw5284step0 = injectiveMoment H raw5284step1 := by
      have hz : ∀ i, raw5284step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw5284step1 = (fun i j => raw5284step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5284step0 permutation80 hz
    injectiveMoment H raw5284step1 = injectiveMoment H raw5284step2 := by
      have heq : raw5284step2 = (fun i j => raw5284step1 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5284step1 permutation29 permutation18
    _ = injectiveMoment H node1237 := by rfl

def raw5285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, -2, 1, -1]]

def raw5285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw5285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2], ![-2, 1, 1], ![2, -1, -1]]

def raw5285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5285 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5285 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw5285 = injectiveMoment H raw5285step0 := by
      have heq : raw5285step0 = raw5285.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5285).symm
    injectiveMoment H raw5285step0 = injectiveMoment H raw5285step1 := by
      have hz : ∀ i, raw5285step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw5285step1 = (fun i j => raw5285step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5285step0 permutation21 hz
    injectiveMoment H raw5285step1 = injectiveMoment H raw5285step2 := by
      have heq : raw5285step2 = (fun i j => raw5285step1 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5285step1 permutation29 permutation6
    _ = injectiveMoment H node279 := by rfl

def raw5286 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

theorem canonical5286 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5286 = injectiveMoment H node2345 := by
  rfl

def raw5287 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical5287 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5287 = injectiveMoment H node2346 := by
  rfl

def raw5288 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5288step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical5288 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5288 = injectiveMoment H node1524 := by
  calc
    injectiveMoment H raw5288 = injectiveMoment H raw5288step0 := by
      have heq : raw5288step0 = (fun i j => raw5288 (permutation33 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5288 permutation33 permutation12
    _ = injectiveMoment H node1524 := by rfl

def raw5289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0]]

def raw5289step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw5289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical5289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5289 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw5289 = injectiveMoment H raw5289step0 := by
      have heq : raw5289step0 = raw5289.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5289).symm
    injectiveMoment H raw5289step0 = injectiveMoment H raw5289step1 := by
      have heq : raw5289step1 = (fun i j => raw5289step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5289step0 permutation29 permutation18
    _ = injectiveMoment H node1027 := by rfl

def raw5290 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical5290 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5290 = injectiveMoment H node2347 := by
  rfl

def raw5291 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw5291step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical5291 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5291 = injectiveMoment H node2347 := by
  calc
    injectiveMoment H raw5291 = injectiveMoment H raw5291step0 := by
      have heq : raw5291step0 = (fun i j => raw5291 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5291 permutation34 permutation9
    _ = injectiveMoment H node2347 := by rfl

def raw5292 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, -1, 1]]

def raw5292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 1, 2, -1], ![2, -1, -2, 1]]

def raw5292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, -1, -2]]

theorem canonical5292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5292 = injectiveMoment H node825 := by
  calc
    injectiveMoment H raw5292 = injectiveMoment H raw5292step0 := by
      have heq : raw5292step0 = raw5292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5292).symm
    injectiveMoment H raw5292step0 = injectiveMoment H raw5292step1 := by
      have heq : raw5292step1 = (fun i j => raw5292step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5292step0 permutation29 permutation18
    _ = injectiveMoment H node825 := by rfl

def raw5293 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, -1, 2], ![2, -1, 1, -2]]

def raw5293step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical5293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5293 = injectiveMoment H node1331 := by
  calc
    injectiveMoment H raw5293 = injectiveMoment H raw5293step0 := by
      have heq : raw5293step0 = raw5293.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5293).symm
    injectiveMoment H raw5293step0 = injectiveMoment H raw5293step1 := by
      have heq : raw5293step1 = (fun i j => raw5293step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5293step0 permutation29 permutation18
    _ = injectiveMoment H node1331 := by rfl

def raw5294 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5294step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw5294step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical5294 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5294 = injectiveMoment H node1237 := by
  calc
    injectiveMoment H raw5294 = injectiveMoment H raw5294step0 := by
      have heq : raw5294step0 = raw5294.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5294).symm
    injectiveMoment H raw5294step0 = injectiveMoment H raw5294step1 := by
      have heq : raw5294step1 = (fun i j => raw5294step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5294step0 permutation29 permutation18
    _ = injectiveMoment H node1237 := by rfl

def raw5295 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw5295step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw5295step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical5295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5295 = injectiveMoment H node1237 := by
  calc
    injectiveMoment H raw5295 = injectiveMoment H raw5295step0 := by
      have heq : raw5295step0 = raw5295.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5295).symm
    injectiveMoment H raw5295step0 = injectiveMoment H raw5295step1 := by
      have heq : raw5295step1 = (fun i j => raw5295step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5295step0 permutation29 permutation20
    _ = injectiveMoment H node1237 := by rfl

def raw5296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5296step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 2, 1, -1], ![2, -2, -1, 1]]

def raw5296step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, -1, -2]]

theorem canonical5296 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5296 = injectiveMoment H node825 := by
  calc
    injectiveMoment H raw5296 = injectiveMoment H raw5296step0 := by
      have heq : raw5296step0 = raw5296.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5296).symm
    injectiveMoment H raw5296step0 = injectiveMoment H raw5296step1 := by
      have heq : raw5296step1 = (fun i j => raw5296step0 (permutation29 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5296step0 permutation29 permutation24
    _ = injectiveMoment H node825 := by rfl

def raw5297 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw5297step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, 2, 1, -1], ![2, -2, 0, 0]]

def raw5297step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1], ![-2, 2, 0, 0]]

def raw5297step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical5297 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5297 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw5297 = injectiveMoment H raw5297step0 := by
      have heq : raw5297step0 = raw5297.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5297).symm
    injectiveMoment H raw5297step0 = injectiveMoment H raw5297step1 := by
      have heq : raw5297step1 = -raw5297step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5297step0).symm
    injectiveMoment H raw5297step1 = injectiveMoment H raw5297step2 := by
      have heq : raw5297step2 = (fun i j => raw5297step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5297step1 permutation13 permutation32
    _ = injectiveMoment H node1059 := by rfl

def raw5298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 2, -1, 1], ![2, -2, 1, -1]]

def raw5298step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical5298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5298 = injectiveMoment H node497 := by
  calc
    injectiveMoment H raw5298 = injectiveMoment H raw5298step0 := by
      have heq : raw5298step0 = raw5298.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5298).symm
    injectiveMoment H raw5298step0 = injectiveMoment H raw5298step1 := by
      have heq : raw5298step1 = (fun i j => raw5298step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5298step0 permutation29 permutation20
    _ = injectiveMoment H node497 := by rfl

def raw5299 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5299step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0], ![2, -2, 0, 0]]

def raw5299step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical5299 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5299 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw5299 = injectiveMoment H raw5299step0 := by
      have heq : raw5299step0 = raw5299.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5299).symm
    injectiveMoment H raw5299step0 = injectiveMoment H raw5299step1 := by
      have heq : raw5299step1 = (fun i j => raw5299step0 (permutation20 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5299step0 permutation20 permutation26
    _ = injectiveMoment H node1027 := by rfl

def raw5300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw5300step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, 3, 0, -1], ![2, -3, 1, 0]]

def raw5300step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![2, -3, 0, 1], ![-2, 3, -1, 0]]

def raw5300step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -3, 2]]

theorem canonical5300 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5300 = injectiveMoment H node1017 := by
  calc
    injectiveMoment H raw5300 = injectiveMoment H raw5300step0 := by
      have heq : raw5300step0 = raw5300.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5300).symm
    injectiveMoment H raw5300step0 = injectiveMoment H raw5300step1 := by
      have heq : raw5300step1 = -raw5300step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5300step0).symm
    injectiveMoment H raw5300step1 = injectiveMoment H raw5300step2 := by
      have heq : raw5300step2 = (fun i j => raw5300step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5300step1 permutation13 permutation32
    _ = injectiveMoment H node1017 := by rfl

def raw5301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5301step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 3, -1, 0], ![2, -3, 1, 0]]

def raw5301step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, 1, 0, -2]]

theorem canonical5301 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5301 = injectiveMoment H node1012 := by
  calc
    injectiveMoment H raw5301 = injectiveMoment H raw5301step0 := by
      have heq : raw5301step0 = raw5301.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5301).symm
    injectiveMoment H raw5301step0 = injectiveMoment H raw5301step1 := by
      have heq : raw5301step1 = (fun i j => raw5301step0 (permutation18 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5301step0 permutation18 permutation32
    _ = injectiveMoment H node1012 := by rfl

def raw5302 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![1, -2, -1, 2], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw5302step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -2, 0, 0], ![-2, -1, 2, 1], ![2, 2, -2, -2]]

def raw5302step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical5302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5302 = injectiveMoment H node410 := by
  calc
    injectiveMoment H raw5302 = injectiveMoment H raw5302step0 := by
      have heq : raw5302step0 = raw5302.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5302).symm
    injectiveMoment H raw5302step0 = injectiveMoment H raw5302step1 := by
      have heq : raw5302step1 = (fun i j => raw5302step0 (permutation29 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5302step0 permutation29 permutation26
    _ = injectiveMoment H node410 := by rfl

def raw5303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![1, -1, -1, 1], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw5303step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, -1, 0], ![-2, -1, 2, 1], ![2, 1, -1, -2]]

def raw5303step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]

theorem canonical5303 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5303 = injectiveMoment H node500 := by
  calc
    injectiveMoment H raw5303 = injectiveMoment H raw5303step0 := by
      have heq : raw5303step0 = raw5303.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5303).symm
    injectiveMoment H raw5303step0 = injectiveMoment H raw5303step1 := by
      have heq : raw5303step1 = (fun i j => raw5303step0 (permutation29 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5303step0 permutation29 permutation32
    _ = injectiveMoment H node500 := by rfl

def raw5304 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![1, -1, -1, 1], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def raw5304step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, -1, 0], ![-2, -1, 3, 0], ![2, 1, -2, -1]]

def raw5304step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-2, 1, 1, 0], ![2, 1, -3, 0], ![-2, -1, 2, 1]]

def raw5304step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical5304 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5304 = injectiveMoment H node1073 := by
  calc
    injectiveMoment H raw5304 = injectiveMoment H raw5304step0 := by
      have heq : raw5304step0 = raw5304.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5304).symm
    injectiveMoment H raw5304step0 = injectiveMoment H raw5304step1 := by
      have heq : raw5304step1 = -raw5304step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5304step0).symm
    injectiveMoment H raw5304step1 = injectiveMoment H raw5304step2 := by
      have heq : raw5304step2 = (fun i j => raw5304step1 (permutation11 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5304step1 permutation11 permutation30
    _ = injectiveMoment H node1073 := by rfl

def raw5305 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5305step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, -2, 0, 3], ![1, 3, 0, -4]]

def raw5305step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, -1, 3], ![0, 3, 1, -4], ![1, 0, -2, 1]]

theorem canonical5305 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5305 = injectiveMoment H node1154 := by
  calc
    injectiveMoment H raw5305 = injectiveMoment H raw5305step0 := by
      have heq : raw5305step0 = raw5305.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5305).symm
    injectiveMoment H raw5305step0 = injectiveMoment H raw5305step1 := by
      have heq : raw5305step1 = (fun i j => raw5305step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5305step0 permutation18 permutation23
    _ = injectiveMoment H node1154 := by rfl

def raw5306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5306step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical5306 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5306 = injectiveMoment H node1837 := by
  calc
    injectiveMoment H raw5306 = injectiveMoment H raw5306step0 := by
      have heq : raw5306step0 = (fun i j => raw5306 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5306 permutation33 permutation11
    _ = injectiveMoment H node1837 := by rfl

def raw5307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical5307 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5307 = injectiveMoment H node2348 := by
  rfl

def raw5308 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw5308step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, -1, -1, 3], ![1, 2, 1, -4]]

def raw5308step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![1, 1, 1, -3], ![-1, -2, -1, 4]]

def raw5308step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

theorem canonical5308 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5308 = injectiveMoment H node453 := by
  calc
    injectiveMoment H raw5308 = injectiveMoment H raw5308step0 := by
      have heq : raw5308step0 = raw5308.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5308).symm
    injectiveMoment H raw5308step0 = injectiveMoment H raw5308step1 := by
      have heq : raw5308step1 = -raw5308step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5308step0).symm
    injectiveMoment H raw5308step1 = injectiveMoment H raw5308step2 := by
      have heq : raw5308step2 = (fun i j => raw5308step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5308step1 permutation27 permutation17
    _ = injectiveMoment H node453 := by rfl

def raw5309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, -1, 0, 2], ![1, 2, 0, -3]]

def raw5309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical5309 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5309 = injectiveMoment H node1007 := by
  calc
    injectiveMoment H raw5309 = injectiveMoment H raw5309step0 := by
      have heq : raw5309step0 = raw5309.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5309).symm
    injectiveMoment H raw5309step0 = injectiveMoment H raw5309step1 := by
      have heq : raw5309step1 = (fun i j => raw5309step0 (permutation18 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5309step0 permutation18 permutation24
    _ = injectiveMoment H node1007 := by rfl

def raw5310 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5310step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical5310 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5310 = injectiveMoment H node522 := by
  calc
    injectiveMoment H raw5310 = injectiveMoment H raw5310step0 := by
      have heq : raw5310step0 = (fun i j => raw5310 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5310 permutation9 permutation11
    _ = injectiveMoment H node522 := by rfl

def raw5311 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw5311step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, -1, 3, -1], ![1, 2, -3, 0]]

def raw5311step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical5311 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5311 = injectiveMoment H node947 := by
  calc
    injectiveMoment H raw5311 = injectiveMoment H raw5311step0 := by
      have heq : raw5311step0 = raw5311.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5311).symm
    injectiveMoment H raw5311step0 = injectiveMoment H raw5311step1 := by
      have heq : raw5311step1 = (fun i j => raw5311step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5311step0 permutation24 permutation29
    _ = injectiveMoment H node947 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
