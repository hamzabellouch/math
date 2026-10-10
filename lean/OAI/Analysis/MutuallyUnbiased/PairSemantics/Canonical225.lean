import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7200 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7200step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, -1, -3, 4], ![-1, 1, 1, -1]]

def raw7200step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical7200 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7200 = injectiveMoment H node1176 := by
  calc
    injectiveMoment H raw7200 = injectiveMoment H raw7200step0 := by
      have heq : raw7200step0 = -raw7200 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7200).symm
    injectiveMoment H raw7200step0 = injectiveMoment H raw7200step1 := by
      have heq : raw7200step1 = (fun i j => raw7200step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7200step0 permutation23 permutation15
    _ = injectiveMoment H node1176 := by rfl

def raw7201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw7201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3], ![2, 1, -1, -2]]

def raw7201step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![1, 1, 1, -3], ![-2, -1, 1, 2]]

def raw7201step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

theorem canonical7201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7201 = injectiveMoment H node827 := by
  calc
    injectiveMoment H raw7201 = injectiveMoment H raw7201step0 := by
      have heq : raw7201step0 = raw7201.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7201).symm
    injectiveMoment H raw7201step0 = injectiveMoment H raw7201step1 := by
      have heq : raw7201step1 = -raw7201step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7201step0).symm
    injectiveMoment H raw7201step1 = injectiveMoment H raw7201step2 := by
      have heq : raw7201step2 = (fun i j => raw7201step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7201step1 permutation29 permutation15
    _ = injectiveMoment H node827 := by rfl

def raw7202 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7202step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -1, 2, 0], ![2, 1, -4, 1]]

def raw7202step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![1, 1, -2, 0], ![-2, -1, 4, -1]]

def raw7202step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical7202 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7202 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw7202 = injectiveMoment H raw7202step0 := by
      have heq : raw7202step0 = raw7202.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7202).symm
    injectiveMoment H raw7202step0 = injectiveMoment H raw7202step1 := by
      have heq : raw7202step1 = -raw7202step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7202step0).symm
    injectiveMoment H raw7202step1 = injectiveMoment H raw7202step2 := by
      have heq : raw7202step2 = (fun i j => raw7202step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7202step1 permutation29 permutation16
    _ = injectiveMoment H node771 := by rfl

def raw7203 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def raw7203step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![0, -1, -3, 4]]

def raw7203step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical7203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7203 = injectiveMoment H node3411 := by
  calc
    injectiveMoment H raw7203 = injectiveMoment H raw7203step0 := by
      have heq : raw7203step0 = -raw7203 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7203).symm
    injectiveMoment H raw7203step0 = injectiveMoment H raw7203step1 := by
      have heq : raw7203step1 = (fun i j => raw7203step0 (permutation398 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7203step0 permutation398 permutation15
    _ = injectiveMoment H node3411 := by rfl

def raw7204 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def raw7204step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![0, -2, -2, 4]]

def raw7204step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical7204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7204 = injectiveMoment H node3112 := by
  calc
    injectiveMoment H raw7204 = injectiveMoment H raw7204step0 := by
      have heq : raw7204step0 = -raw7204 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7204).symm
    injectiveMoment H raw7204step0 = injectiveMoment H raw7204step1 := by
      have heq : raw7204step1 = (fun i j => raw7204step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7204step0 permutation377 permutation15
    _ = injectiveMoment H node3112 := by rfl

def raw7205 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7205step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 0, 2, -1], ![2, 0, -3, 1]]

def raw7205step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![1, 0, -2, 1], ![-2, 0, 3, -1]]

def raw7205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 3, -1]]

def raw7205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7205 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7205 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw7205 = injectiveMoment H raw7205step0 := by
      have heq : raw7205step0 = raw7205.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7205).symm
    injectiveMoment H raw7205step0 = injectiveMoment H raw7205step1 := by
      have heq : raw7205step1 = -raw7205step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7205step0).symm
    injectiveMoment H raw7205step1 = injectiveMoment H raw7205step2 := by
      have hz : ∀ i, raw7205step1 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7205step2 = (fun i j => raw7205step1 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7205step1 permutation15 hz
    injectiveMoment H raw7205step2 = injectiveMoment H raw7205step3 := by
      have heq : raw7205step3 = (fun i j => raw7205step2 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7205step2 permutation29 permutation4
    _ = injectiveMoment H node181 := by rfl

def raw7206 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 0, 0], ![1, 0, 1, -2]]

def raw7206step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]

def raw7206step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]

def raw7206step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7206step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7206 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7206 = injectiveMoment H raw7206step0 := by
      have heq : raw7206step0 = raw7206.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7206).symm
    injectiveMoment H raw7206step0 = injectiveMoment H raw7206step1 := by
      have hz : ∀ j, raw7206step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7206step1 = (fun i j => raw7206step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7206step0 permutation15 hz
    injectiveMoment H raw7206step1 = injectiveMoment H raw7206step2 := by
      have hz : ∀ i, raw7206step1 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7206step2 = (fun i j => raw7206step1 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7206step1 permutation5 hz
    injectiveMoment H raw7206step2 = injectiveMoment H raw7206step3 := by
      have heq : raw7206step3 = (fun i j => raw7206step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7206step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7207 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, 0, -1]]

def raw7207step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw7207step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7207 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7207 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw7207 = injectiveMoment H raw7207step0 := by
      have hz : ∀ j, raw7207 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7207step0 = (fun i j => raw7207 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7207 permutation21 hz
    injectiveMoment H raw7207step0 = injectiveMoment H raw7207step1 := by
      have hz : ∀ i, raw7207step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7207step1 = (fun i j => raw7207step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7207step0 permutation15 hz
    _ = injectiveMoment H node61 := by rfl

def raw7208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical7208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7208 = injectiveMoment H node2734 := by
  rfl

def raw7209 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0]]

def raw7209step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7209 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7209 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw7209 = injectiveMoment H raw7209step0 := by
      have hz : ∀ i, raw7209 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7209step0 = (fun i j => raw7209 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7209 permutation15 hz
    _ = injectiveMoment H node287 := by rfl

def raw7210 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical7210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7210 = injectiveMoment H node1262 := by
  rfl

def raw7211 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7211step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7211 = injectiveMoment H node1048 := by
  calc
    injectiveMoment H raw7211 = injectiveMoment H raw7211step0 := by
      have heq : raw7211step0 = (fun i j => raw7211 (permutation12 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7211 permutation12 permutation21
    _ = injectiveMoment H node1048 := by rfl

def raw7212 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw7212step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 2, -1, 0]]

def raw7212step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical7212 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7212 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw7212 = injectiveMoment H raw7212step0 := by
      have heq : raw7212step0 = -raw7212 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7212).symm
    injectiveMoment H raw7212step0 = injectiveMoment H raw7212step1 := by
      have heq : raw7212step1 = (fun i j => raw7212step0 (permutation30 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7212step0 permutation30 permutation12
    _ = injectiveMoment H node1000 := by rfl

def raw7213 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw7213step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7213 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw7213 = injectiveMoment H raw7213step0 := by
      have hz : ∀ i, raw7213 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7213step0 = (fun i j => raw7213 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7213 permutation15 hz
    _ = injectiveMoment H node61 := by rfl

def raw7214 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

theorem canonical7214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7214 = injectiveMoment H node1263 := by
  rfl

def raw7215 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical7215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7215 = injectiveMoment H node1264 := by
  rfl

def raw7216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical7216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7216 = injectiveMoment H node1265 := by
  rfl

def raw7217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0]]

def raw7217step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

theorem canonical7217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7217 = injectiveMoment H node1314 := by
  calc
    injectiveMoment H raw7217 = injectiveMoment H raw7217step0 := by
      have heq : raw7217step0 = (fun i j => raw7217 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7217 permutation9 permutation10
    _ = injectiveMoment H node1314 := by rfl

def raw7218 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw7218step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7218 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw7218 = injectiveMoment H raw7218step0 := by
      have hz : ∀ i, raw7218 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7218step0 = (fun i j => raw7218 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7218 permutation15 hz
    _ = injectiveMoment H node62 := by rfl

def raw7219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

theorem canonical7219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7219 = injectiveMoment H node1267 := by
  rfl

def raw7220 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

theorem canonical7220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7220 = injectiveMoment H node2735 := by
  rfl

def raw7221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical7221 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7221 = injectiveMoment H node1268 := by
  rfl

def raw7222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

theorem canonical7222 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7222 = injectiveMoment H node1269 := by
  rfl

def raw7223 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![1, 0, -2, 1]]

def raw7223step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical7223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7223 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw7223 = injectiveMoment H raw7223step0 := by
      have hz : ∀ i, raw7223 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7223step0 = (fun i j => raw7223 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7223 permutation15 hz
    _ = injectiveMoment H node63 := by rfl

def raw7224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 0, 1, -1], ![1, -1, 2, -2]]

def raw7224step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

theorem canonical7224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7224 = injectiveMoment H node1261 := by
  calc
    injectiveMoment H raw7224 = injectiveMoment H raw7224step0 := by
      have heq : raw7224step0 = (fun i j => raw7224 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7224 permutation11 permutation9
    _ = injectiveMoment H node1261 := by rfl

def raw7225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

theorem canonical7225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7225 = injectiveMoment H node1267 := by
  calc
    injectiveMoment H raw7225 = injectiveMoment H raw7225step0 := by
      have heq : raw7225step0 = (fun i j => raw7225 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7225 permutation11 permutation9
    _ = injectiveMoment H node1267 := by rfl

def raw7226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7226step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -2, 0, 3], ![2, 1, -1, -2]]

def raw7226step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![1, 2, 0, -3], ![-2, -1, 1, 2]]

def raw7226step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical7226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7226 = injectiveMoment H node1050 := by
  calc
    injectiveMoment H raw7226 = injectiveMoment H raw7226step0 := by
      have heq : raw7226step0 = raw7226.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7226).symm
    injectiveMoment H raw7226step0 = injectiveMoment H raw7226step1 := by
      have heq : raw7226step1 = -raw7226step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7226step0).symm
    injectiveMoment H raw7226step1 = injectiveMoment H raw7226step2 := by
      have heq : raw7226step2 = (fun i j => raw7226step1 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7226step1 permutation15 permutation23
    _ = injectiveMoment H node1050 := by rfl

def raw7227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical7227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7227 = injectiveMoment H node1276 := by
  rfl

def raw7228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical7228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7228 = injectiveMoment H node1277 := by
  rfl

def raw7229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical7229 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7229 = injectiveMoment H node1278 := by
  rfl

def raw7230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![0, 0, 2, -2]]

def raw7230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

theorem canonical7230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7230 = injectiveMoment H node1263 := by
  calc
    injectiveMoment H raw7230 = injectiveMoment H raw7230step0 := by
      have heq : raw7230step0 = (fun i j => raw7230 (permutation13 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7230 permutation13 permutation9
    _ = injectiveMoment H node1263 := by rfl

def raw7231 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw7231step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, -2, 3], ![2, 1, -3]]

def raw7231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7231 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw7231 = injectiveMoment H raw7231step0 := by
      have heq : raw7231step0 = raw7231.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7231).symm
    injectiveMoment H raw7231step0 = injectiveMoment H raw7231step1 := by
      have heq : raw7231step1 = (fun i j => raw7231step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7231step0 permutation21 permutation5
    _ = injectiveMoment H node174 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
