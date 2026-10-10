import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraPermutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw80 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 1, -1]]

def extraRaw80step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 1, -1]]

def extraRaw80step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem extraCanonical80 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw80 = injectiveMoment H node659 := by
  calc
    injectiveMoment H extraRaw80 = injectiveMoment H extraRaw80step0 := by
      have hz : ∀ j, extraRaw80 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw80step0 = (fun u v => extraRaw80 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw80 extraPermutation62 hz
    injectiveMoment H extraRaw80step0 = injectiveMoment H extraRaw80step1 := by
      have heq : extraRaw80step1 = (fun u v => extraRaw80step0 (extraPermutation47 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw80step0 extraPermutation47 extraPermutation3
    _ = injectiveMoment H node659 := by rfl

def extraRaw81 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]

def extraRaw81step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw81step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw81step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical81 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw81 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw81 = injectiveMoment H extraRaw81step0 := by
      have hz : ∀ j, extraRaw81 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw81step0 = (fun u v => extraRaw81 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw81 extraPermutation66 hz
    injectiveMoment H extraRaw81step0 = injectiveMoment H extraRaw81step1 := by
      have hz : ∀ j, extraRaw81step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw81step1 = (fun u v => extraRaw81step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw81step0 extraPermutation39 hz
    injectiveMoment H extraRaw81step1 = injectiveMoment H extraRaw81step2 := by
      have hz : ∀ j, extraRaw81step1 j (extraPermutation4 0) = 0 := by decide +kernel
      have heq : extraRaw81step2 = (fun u v => extraRaw81step1 u (extraPermutation4 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw81step1 extraPermutation4 hz
    _ = injectiveMoment H node65 := by rfl

def extraRaw82 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![1, 1, -1, -1]]

def extraRaw82step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![0, 2, 0, -2], ![1, 1, -1, -1]]

def extraRaw82step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem extraCanonical82 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw82 = injectiveMoment H node2839 := by
  calc
    injectiveMoment H extraRaw82 = injectiveMoment H extraRaw82step0 := by
      have hz : ∀ j, extraRaw82 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw82step0 = (fun u v => extraRaw82 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw82 extraPermutation62 hz
    injectiveMoment H extraRaw82step0 = injectiveMoment H extraRaw82step1 := by
      have heq : extraRaw82step1 = (fun u v => extraRaw82step0 (extraPermutation26 u) (extraPermutation10 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw82step0 extraPermutation26 extraPermutation10
    _ = injectiveMoment H node2839 := by rfl

def extraRaw83 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical83 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw83 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw83 = injectiveMoment H extraRaw83step0 := by
      have hz : ∀ j, extraRaw83 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw83step0 = (fun u v => extraRaw83 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw83 extraPermutation63 hz
    injectiveMoment H extraRaw83step0 = injectiveMoment H extraRaw83step1 := by
      have hz : ∀ j, extraRaw83step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw83step1 = (fun u v => extraRaw83step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw83step0 extraPermutation39 hz
    injectiveMoment H extraRaw83step1 = injectiveMoment H extraRaw83step2 := by
      have hz : ∀ j, extraRaw83step1 (extraPermutation12 0) j = 0 := by decide +kernel
      have heq : extraRaw83step2 = (fun u v => extraRaw83step1 (extraPermutation12 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw83step1 extraPermutation12 hz
    injectiveMoment H extraRaw83step2 = injectiveMoment H extraRaw83step3 := by
      have hz : ∀ j, extraRaw83step2 (extraPermutation2 0) j = 0 := by decide +kernel
      have heq : extraRaw83step3 = (fun u v => extraRaw83step2 (extraPermutation2 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw83step2 extraPermutation2 hz
    _ = injectiveMoment H node5 := by rfl

def extraRaw84 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2]]

def extraRaw84step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2]]

def extraRaw84step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2]]

def extraRaw84step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem extraCanonical84 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw84 = injectiveMoment H node288 := by
  calc
    injectiveMoment H extraRaw84 = injectiveMoment H extraRaw84step0 := by
      have hz : ∀ j, extraRaw84 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw84step0 = (fun u v => extraRaw84 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw84 extraPermutation63 hz
    injectiveMoment H extraRaw84step0 = injectiveMoment H extraRaw84step1 := by
      have hz : ∀ j, extraRaw84step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw84step1 = (fun u v => extraRaw84step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw84step0 extraPermutation39 hz
    injectiveMoment H extraRaw84step1 = injectiveMoment H extraRaw84step2 := by
      have heq : extraRaw84step2 = (fun u v => extraRaw84step1 (extraPermutation17 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw84step1 extraPermutation17 extraPermutation3
    _ = injectiveMoment H node288 := by rfl

def extraRaw85 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw85step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw85step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw85step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical85 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw85 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw85 = injectiveMoment H extraRaw85step0 := by
      have hz : ∀ j, extraRaw85 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw85step0 = (fun u v => extraRaw85 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw85 extraPermutation62 hz
    injectiveMoment H extraRaw85step0 = injectiveMoment H extraRaw85step1 := by
      have hz : ∀ j, extraRaw85step0 (extraPermutation34 0) j = 0 := by decide +kernel
      have heq : extraRaw85step1 = (fun u v => extraRaw85step0 (extraPermutation34 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw85step0 extraPermutation34 hz
    injectiveMoment H extraRaw85step1 = injectiveMoment H extraRaw85step2 := by
      have heq : extraRaw85step2 = (fun u v => extraRaw85step1 (extraPermutation18 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw85step1 extraPermutation18 extraPermutation0
    _ = injectiveMoment H node65 := by rfl

def extraRaw86 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw86step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw86step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem extraCanonical86 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw86 = injectiveMoment H node1135 := by
  calc
    injectiveMoment H extraRaw86 = injectiveMoment H extraRaw86step0 := by
      have hz : ∀ j, extraRaw86 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw86step0 = (fun u v => extraRaw86 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw86 extraPermutation62 hz
    injectiveMoment H extraRaw86step0 = injectiveMoment H extraRaw86step1 := by
      have heq : extraRaw86step1 = (fun u v => extraRaw86step0 (extraPermutation26 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw86step0 extraPermutation26 extraPermutation2
    _ = injectiveMoment H node1135 := by rfl

def extraRaw87 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0]]

def extraRaw87step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0]]

def extraRaw87step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem extraCanonical87 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw87 = injectiveMoment H node1135 := by
  calc
    injectiveMoment H extraRaw87 = injectiveMoment H extraRaw87step0 := by
      have hz : ∀ j, extraRaw87 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw87step0 = (fun u v => extraRaw87 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw87 extraPermutation62 hz
    injectiveMoment H extraRaw87step0 = injectiveMoment H extraRaw87step1 := by
      have heq : extraRaw87step1 = (fun u v => extraRaw87step0 (extraPermutation47 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw87step0 extraPermutation47 extraPermutation3
    _ = injectiveMoment H node1135 := by rfl

def extraRaw88 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw88step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw88step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem extraCanonical88 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw88 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H extraRaw88 = injectiveMoment H extraRaw88step0 := by
      have hz : ∀ j, extraRaw88 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw88step0 = (fun u v => extraRaw88 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw88 extraPermutation62 hz
    injectiveMoment H extraRaw88step0 = injectiveMoment H extraRaw88step1 := by
      have heq : extraRaw88step1 = (fun u v => extraRaw88step0 (extraPermutation50 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw88step0 extraPermutation50 extraPermutation5
    _ = injectiveMoment H node1294 := by rfl

def extraRaw89 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![1, 1, 0, -2]]

def extraRaw89step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![0, 2, -1, -1], ![1, 1, 0, -2]]

def extraRaw89step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem extraCanonical89 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw89 = injectiveMoment H node2712 := by
  calc
    injectiveMoment H extraRaw89 = injectiveMoment H extraRaw89step0 := by
      have hz : ∀ j, extraRaw89 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw89step0 = (fun u v => extraRaw89 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw89 extraPermutation62 hz
    injectiveMoment H extraRaw89step0 = injectiveMoment H extraRaw89step1 := by
      have heq : extraRaw89step1 = (fun u v => extraRaw89step0 (extraPermutation44 u) (extraPermutation16 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw89step0 extraPermutation44 extraPermutation16
    _ = injectiveMoment H node2712 := by rfl

def extraRaw90 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2]]

def extraRaw90step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-1, 1], ![-2, 2]]

def extraRaw90step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-2, 2]]

def extraRaw90step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem extraCanonical90 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw90 = injectiveMoment H node46 := by
  calc
    injectiveMoment H extraRaw90 = injectiveMoment H extraRaw90step0 := by
      have hz : ∀ j, extraRaw90 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw90step0 = (fun u v => extraRaw90 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw90 extraPermutation63 hz
    injectiveMoment H extraRaw90step0 = injectiveMoment H extraRaw90step1 := by
      have hz : ∀ j, extraRaw90step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw90step1 = (fun u v => extraRaw90step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw90step0 extraPermutation39 hz
    injectiveMoment H extraRaw90step1 = injectiveMoment H extraRaw90step2 := by
      have heq : extraRaw90step2 = (fun u v => extraRaw90step1 (extraPermutation23 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw90step1 extraPermutation23 extraPermutation0
    _ = injectiveMoment H node46 := by rfl

def extraRaw91 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![0, 2, -2]]

def extraRaw91step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![0, 2, -2]]

def extraRaw91step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem extraCanonical91 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw91 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw91 = injectiveMoment H extraRaw91step0 := by
      have hz : ∀ j, extraRaw91 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw91step0 = (fun u v => extraRaw91 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw91 extraPermutation62 hz
    injectiveMoment H extraRaw91step0 = injectiveMoment H extraRaw91step1 := by
      have heq : extraRaw91step1 = (fun u v => extraRaw91step0 (extraPermutation28 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw91step0 extraPermutation28 extraPermutation2
    _ = injectiveMoment H node858 := by rfl

def extraRaw92 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw92step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw92step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw92step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw92step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw92step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical92 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw92 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw92 = injectiveMoment H extraRaw92step0 := by
      have hz : ∀ j, extraRaw92 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw92step0 = (fun u v => extraRaw92 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw92 extraPermutation66 hz
    injectiveMoment H extraRaw92step0 = injectiveMoment H extraRaw92step1 := by
      have hz : ∀ j, extraRaw92step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw92step1 = (fun u v => extraRaw92step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw92step0 extraPermutation39 hz
    injectiveMoment H extraRaw92step1 = injectiveMoment H extraRaw92step2 := by
      have hz : ∀ j, extraRaw92step1 (extraPermutation12 0) j = 0 := by decide +kernel
      have heq : extraRaw92step2 = (fun u v => extraRaw92step1 (extraPermutation12 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw92step1 extraPermutation12 hz
    injectiveMoment H extraRaw92step2 = injectiveMoment H extraRaw92step3 := by
      have hz : ∀ j, extraRaw92step2 (extraPermutation2 0) j = 0 := by decide +kernel
      have heq : extraRaw92step3 = (fun u v => extraRaw92step2 (extraPermutation2 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw92step2 extraPermutation2 hz
    injectiveMoment H extraRaw92step3 = injectiveMoment H extraRaw92step4 := by
      have heq : extraRaw92step4 = (fun u v => extraRaw92step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw92step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw93 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw93step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw93step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem extraCanonical93 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw93 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H extraRaw93 = injectiveMoment H extraRaw93step0 := by
      have hz : ∀ j, extraRaw93 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw93step0 = (fun u v => extraRaw93 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw93 extraPermutation62 hz
    injectiveMoment H extraRaw93step0 = injectiveMoment H extraRaw93step1 := by
      have heq : extraRaw93step1 = (fun u v => extraRaw93step0 (extraPermutation53 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw93step0 extraPermutation53 extraPermutation3
    _ = injectiveMoment H node1152 := by rfl

def extraRaw94 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw94step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw94step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical94 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw94 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw94 = injectiveMoment H extraRaw94step0 := by
      have hz : ∀ j, extraRaw94 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw94step0 = (fun u v => extraRaw94 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw94 extraPermutation62 hz
    injectiveMoment H extraRaw94step0 = injectiveMoment H extraRaw94step1 := by
      have heq : extraRaw94step1 = (fun u v => extraRaw94step0 (extraPermutation24 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw94step0 extraPermutation24 extraPermutation4
    _ = injectiveMoment H node1151 := by rfl

def extraRaw95 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw95step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw95step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw95step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem extraCanonical95 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw95 = injectiveMoment H node283 := by
  calc
    injectiveMoment H extraRaw95 = injectiveMoment H extraRaw95step0 := by
      have hz : ∀ j, extraRaw95 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw95step0 = (fun u v => extraRaw95 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw95 extraPermutation63 hz
    injectiveMoment H extraRaw95step0 = injectiveMoment H extraRaw95step1 := by
      have hz : ∀ j, extraRaw95step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw95step1 = (fun u v => extraRaw95step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw95step0 extraPermutation39 hz
    injectiveMoment H extraRaw95step1 = injectiveMoment H extraRaw95step2 := by
      have heq : extraRaw95step2 = (fun u v => extraRaw95step1 (extraPermutation23 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw95step1 extraPermutation23 extraPermutation3
    _ = injectiveMoment H node283 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
