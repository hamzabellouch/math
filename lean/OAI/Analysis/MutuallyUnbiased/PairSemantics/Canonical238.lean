import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7616 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -3, 3]]

def raw7616step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![3, 0, -3], ![-2, -1, 3]]

def raw7616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7616 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7616 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw7616 = injectiveMoment H raw7616step0 := by
      have heq : raw7616step0 = raw7616.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7616).symm
    injectiveMoment H raw7616step0 = injectiveMoment H raw7616step1 := by
      have heq : raw7616step1 = (fun i j => raw7616step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7616step0 permutation28 permutation5
    _ = injectiveMoment H node269 := by rfl

def raw7617 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -2, -3, 4]]

def raw7617step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![3, 0, -3], ![-2, -2, 4]]

def raw7617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical7617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7617 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw7617 = injectiveMoment H raw7617step0 := by
      have heq : raw7617step0 = raw7617.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7617).symm
    injectiveMoment H raw7617step0 = injectiveMoment H raw7617step1 := by
      have heq : raw7617step1 = (fun i j => raw7617step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7617step0 permutation28 permutation5
    _ = injectiveMoment H node141 := by rfl

def raw7618 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![1, -3, 1, 1], ![0, 3, -4, 1]]

def raw7618step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![3, 1, -4], ![-2, 1, 1]]

def raw7618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-3, -1, 4], ![2, -1, -1]]

def raw7618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical7618 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7618 = injectiveMoment H node87 := by
  calc
    injectiveMoment H raw7618 = injectiveMoment H raw7618step0 := by
      have heq : raw7618step0 = raw7618.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7618).symm
    injectiveMoment H raw7618step0 = injectiveMoment H raw7618step1 := by
      have heq : raw7618step1 = -raw7618step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7618step0).symm
    injectiveMoment H raw7618step1 = injectiveMoment H raw7618step2 := by
      have heq : raw7618step2 = (fun i j => raw7618step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7618step1 permutation23 permutation3
    _ = injectiveMoment H node87 := by rfl

def raw7619 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![1, -2, 1, 0], ![0, 2, -4, 2]]

def raw7619step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![3, 1, -4], ![-2, 0, 2]]

def raw7619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7619 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7619 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7619 = injectiveMoment H raw7619step0 := by
      have heq : raw7619step0 = raw7619.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7619).symm
    injectiveMoment H raw7619step0 = injectiveMoment H raw7619step1 := by
      have heq : raw7619step1 = (fun i j => raw7619step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7619step0 permutation19 permutation5
    _ = injectiveMoment H node201 := by rfl

def raw7620 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![2, -3, 1, 0], ![-1, 3, -4, 2]]

def raw7620step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -3, 3], ![3, 1, -4], ![-2, 0, 2]]

def raw7620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 3, -3], ![-3, -1, 4], ![2, 0, -2]]

def raw7620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

theorem canonical7620 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7620 = injectiveMoment H node86 := by
  calc
    injectiveMoment H raw7620 = injectiveMoment H raw7620step0 := by
      have heq : raw7620step0 = raw7620.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7620).symm
    injectiveMoment H raw7620step0 = injectiveMoment H raw7620step1 := by
      have heq : raw7620step1 = -raw7620step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7620step0).symm
    injectiveMoment H raw7620step1 = injectiveMoment H raw7620step2 := by
      have heq : raw7620step2 = (fun i j => raw7620step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7620step1 permutation23 permutation3
    _ = injectiveMoment H node86 := by rfl

def raw7621 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![2, -2, 1, -1], ![-1, 2, -4, 3]]

def raw7621step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -2, 2], ![3, 1, -4], ![-2, -1, 3]]

def raw7621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 2, -2], ![-3, -1, 4], ![2, 1, -3]]

def raw7621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical7621 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7621 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw7621 = injectiveMoment H raw7621step0 := by
      have heq : raw7621step0 = raw7621.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7621).symm
    injectiveMoment H raw7621step0 = injectiveMoment H raw7621step1 := by
      have heq : raw7621step1 = -raw7621step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7621step0).symm
    injectiveMoment H raw7621step1 = injectiveMoment H raw7621step2 := by
      have heq : raw7621step2 = (fun i j => raw7621step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7621step1 permutation23 permutation3
    _ = injectiveMoment H node84 := by rfl

def raw7622 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]

def raw7622step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical7622 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7622 = injectiveMoment H node296 := by
  calc
    injectiveMoment H raw7622 = injectiveMoment H raw7622step0 := by
      have heq : raw7622step0 = (fun i j => raw7622 (permutation397 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7622 permutation397 permutation2
    _ = injectiveMoment H node296 := by rfl

def raw7623 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def raw7623step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical7623 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7623 = injectiveMoment H node380 := by
  calc
    injectiveMoment H raw7623 = injectiveMoment H raw7623step0 := by
      have heq : raw7623step0 = (fun i j => raw7623 (permutation397 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7623 permutation397 permutation2
    _ = injectiveMoment H node380 := by rfl

def raw7624 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw7624step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical7624 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7624 = injectiveMoment H node717 := by
  calc
    injectiveMoment H raw7624 = injectiveMoment H raw7624step0 := by
      have heq : raw7624step0 = (fun i j => raw7624 (permutation202 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7624 permutation202 permutation1
    _ = injectiveMoment H node717 := by rfl

def raw7625 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw7625step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7625step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7625 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7625 = injectiveMoment H raw7625step0 := by
      have hz : ∀ j, raw7625 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw7625step0 = (fun i j => raw7625 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7625 permutation221 hz
    injectiveMoment H raw7625step0 = injectiveMoment H raw7625step1 := by
      have heq : raw7625step1 = (fun i j => raw7625step0 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7625step0 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw7626 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]

def raw7626step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7626step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7626 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7626 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7626 = injectiveMoment H raw7626step0 := by
      have hz : ∀ j, raw7626 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw7626step0 = (fun i j => raw7626 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7626 permutation80 hz
    injectiveMoment H raw7626step0 = injectiveMoment H raw7626step1 := by
      have heq : raw7626step1 = (fun i j => raw7626step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7626step0 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7627 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]

def raw7627step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7627step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical7627 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7627 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7627 = injectiveMoment H raw7627step0 := by
      have hz : ∀ j, raw7627 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7627step0 = (fun i j => raw7627 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7627 permutation21 hz
    injectiveMoment H raw7627step0 = injectiveMoment H raw7627step1 := by
      have heq : raw7627step1 = (fun i j => raw7627step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7627step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw7628 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3], ![0, 0]]

def raw7628step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]

def raw7628step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7628step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical7628 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7628 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7628 = injectiveMoment H raw7628step0 := by
      have hz : ∀ j, raw7628 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7628step0 = (fun i j => raw7628 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7628 permutation128 hz
    injectiveMoment H raw7628step0 = injectiveMoment H raw7628step1 := by
      have hz : ∀ j, raw7628step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7628step1 = (fun i j => raw7628step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7628step0 permutation21 hz
    injectiveMoment H raw7628step1 = injectiveMoment H raw7628step2 := by
      have heq : raw7628step2 = (fun i j => raw7628step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7628step1 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw7629 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw7629step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw7629step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7629step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7629 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7629 = injectiveMoment H raw7629step0 := by
      have hz : ∀ j, raw7629 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7629step0 = (fun i j => raw7629 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7629 permutation258 hz
    injectiveMoment H raw7629step0 = injectiveMoment H raw7629step1 := by
      have hz : ∀ j, raw7629step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7629step1 = (fun i j => raw7629step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7629step0 permutation104 hz
    injectiveMoment H raw7629step1 = injectiveMoment H raw7629step2 := by
      have heq : raw7629step2 = (fun i j => raw7629step1 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7629step1 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7630 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw7630step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7630step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7630 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7630 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7630 = injectiveMoment H raw7630step0 := by
      have hz : ∀ j, raw7630 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7630step0 = (fun i j => raw7630 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7630 permutation241 hz
    injectiveMoment H raw7630step0 = injectiveMoment H raw7630step1 := by
      have heq : raw7630step1 = (fun i j => raw7630step0 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7630step0 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw7631 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw7631step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7631step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7631 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7631 = injectiveMoment H raw7631step0 := by
      have hz : ∀ j, raw7631 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7631step0 = (fun i j => raw7631 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7631 permutation104 hz
    injectiveMoment H raw7631step0 = injectiveMoment H raw7631step1 := by
      have heq : raw7631step1 = (fun i j => raw7631step0 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7631step0 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7632 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]

def raw7632step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw7632step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7632step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7632 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7632 = injectiveMoment H raw7632step0 := by
      have hz : ∀ j, raw7632 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7632step0 = (fun i j => raw7632 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7632 permutation308 hz
    injectiveMoment H raw7632step0 = injectiveMoment H raw7632step1 := by
      have hz : ∀ j, raw7632step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7632step1 = (fun i j => raw7632step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7632step0 permutation104 hz
    injectiveMoment H raw7632step1 = injectiveMoment H raw7632step2 := by
      have heq : raw7632step2 = (fun i j => raw7632step1 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7632step1 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7633 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw7633step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7633step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7633 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7633 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7633 = injectiveMoment H raw7633step0 := by
      have hz : ∀ j, raw7633 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7633step0 = (fun i j => raw7633 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7633 permutation258 hz
    injectiveMoment H raw7633step0 = injectiveMoment H raw7633step1 := by
      have heq : raw7633step1 = (fun i j => raw7633step0 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7633step0 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw7634 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7634step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7634 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7634 = injectiveMoment H raw7634step0 := by
      have heq : raw7634step0 = (fun i j => raw7634 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7634 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw7635 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw7635step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7635step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7635 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7635 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7635 = injectiveMoment H raw7635step0 := by
      have hz : ∀ j, raw7635 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7635step0 = (fun i j => raw7635 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7635 permutation308 hz
    injectiveMoment H raw7635step0 = injectiveMoment H raw7635step1 := by
      have heq : raw7635step1 = (fun i j => raw7635step0 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7635step0 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw7636 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7636step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7636 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7636 = injectiveMoment H raw7636step0 := by
      have heq : raw7636step0 = (fun i j => raw7636 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7636 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7637 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![0, 0]]

def raw7637step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7637step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7637 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7637 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7637 = injectiveMoment H raw7637step0 := by
      have hz : ∀ j, raw7637 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7637step0 = (fun i j => raw7637 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7637 permutation128 hz
    injectiveMoment H raw7637step0 = injectiveMoment H raw7637step1 := by
      have heq : raw7637step1 = (fun i j => raw7637step0 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7637step0 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7638 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![0, 0], ![1, -1]]

def raw7638step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7638step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7638 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7638 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7638 = injectiveMoment H raw7638step0 := by
      have hz : ∀ j, raw7638 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7638step0 = (fun i j => raw7638 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7638 permutation104 hz
    injectiveMoment H raw7638step0 = injectiveMoment H raw7638step1 := by
      have heq : raw7638step1 = (fun i j => raw7638step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7638step0 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7639 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7639step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7639 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7639 = injectiveMoment H raw7639step0 := by
      have heq : raw7639step0 = (fun i j => raw7639 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7639 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7640 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]

def raw7640step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7640step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7640 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7640 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7640 = injectiveMoment H raw7640step0 := by
      have hz : ∀ j, raw7640 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7640step0 = (fun i j => raw7640 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7640 permutation128 hz
    injectiveMoment H raw7640step0 = injectiveMoment H raw7640step1 := by
      have heq : raw7640step1 = (fun i j => raw7640step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7640step0 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7641 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0], ![0, 0]]

def raw7641step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]

def raw7641step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7641step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7641 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7641 = injectiveMoment H raw7641step0 := by
      have hz : ∀ j, raw7641 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7641step0 = (fun i j => raw7641 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7641 permutation308 hz
    injectiveMoment H raw7641step0 = injectiveMoment H raw7641step1 := by
      have hz : ∀ j, raw7641step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7641step1 = (fun i j => raw7641step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7641step0 permutation128 hz
    injectiveMoment H raw7641step1 = injectiveMoment H raw7641step2 := by
      have heq : raw7641step2 = (fun i j => raw7641step1 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7641step1 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7642 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7642step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical7642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7642 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7642 = injectiveMoment H raw7642step0 := by
      have heq : raw7642step0 = (fun i j => raw7642 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7642 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw7643 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3], ![0, 0]]

def raw7643step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7643step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical7643 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7643 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7643 = injectiveMoment H raw7643step0 := by
      have hz : ∀ j, raw7643 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7643step0 = (fun i j => raw7643 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7643 permutation27 hz
    injectiveMoment H raw7643step0 = injectiveMoment H raw7643step1 := by
      have heq : raw7643step1 = (fun i j => raw7643step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7643step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw7644 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![4, -4]]

def raw7644step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical7644 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7644 = injectiveMoment H node296 := by
  calc
    injectiveMoment H raw7644 = injectiveMoment H raw7644step0 := by
      have heq : raw7644step0 = (fun i j => raw7644 (permutation396 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7644 permutation396 permutation2
    _ = injectiveMoment H node296 := by rfl

def raw7645 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![3, -3]]

def raw7645step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical7645 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7645 = injectiveMoment H node380 := by
  calc
    injectiveMoment H raw7645 = injectiveMoment H raw7645step0 := by
      have heq : raw7645step0 = (fun i j => raw7645 (permutation396 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7645 permutation396 permutation2
    _ = injectiveMoment H node380 := by rfl

def raw7646 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw7646step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical7646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7646 = injectiveMoment H node717 := by
  calc
    injectiveMoment H raw7646 = injectiveMoment H raw7646step0 := by
      have heq : raw7646step0 = (fun i j => raw7646 (permutation221 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7646 permutation221 permutation1
    _ = injectiveMoment H node717 := by rfl

def raw7647 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]

def raw7647step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical7647 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7647 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw7647 = injectiveMoment H raw7647step0 := by
      have heq : raw7647step0 = (fun i j => raw7647 (permutation122 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7647 permutation122 permutation2
    _ = injectiveMoment H node231 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
