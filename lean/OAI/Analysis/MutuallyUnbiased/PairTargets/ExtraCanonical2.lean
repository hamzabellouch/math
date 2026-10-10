import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraPermutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw32 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]

def extraRaw32step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw32step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw32step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical32 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw32 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw32 = injectiveMoment H extraRaw32step0 := by
      have heq : extraRaw32step0 = -extraRaw32 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw32).symm
    injectiveMoment H extraRaw32step0 = injectiveMoment H extraRaw32step1 := by
      have hz : ∀ j, extraRaw32step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw32step1 = (fun u v => extraRaw32step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw32step0 extraPermutation62 hz
    injectiveMoment H extraRaw32step1 = injectiveMoment H extraRaw32step2 := by
      have heq : extraRaw32step2 = (fun u v => extraRaw32step1 (extraPermutation24 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw32step1 extraPermutation24 extraPermutation3
    _ = injectiveMoment H node1151 := by rfl

def extraRaw33 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw33step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw33step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem extraCanonical33 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw33 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H extraRaw33 = injectiveMoment H extraRaw33step0 := by
      have hz : ∀ j, extraRaw33 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw33step0 = (fun u v => extraRaw33 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw33 extraPermutation62 hz
    injectiveMoment H extraRaw33step0 = injectiveMoment H extraRaw33step1 := by
      have heq : extraRaw33step1 = (fun u v => extraRaw33step0 (extraPermutation52 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw33step0 extraPermutation52 extraPermutation5
    _ = injectiveMoment H node1294 := by rfl

def extraRaw34 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def extraRaw34step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def extraRaw34step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def extraRaw34step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem extraCanonical34 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw34 = injectiveMoment H node2711 := by
  calc
    injectiveMoment H extraRaw34 = injectiveMoment H extraRaw34step0 := by
      have heq : extraRaw34step0 = -extraRaw34 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw34).symm
    injectiveMoment H extraRaw34step0 = injectiveMoment H extraRaw34step1 := by
      have hz : ∀ j, extraRaw34step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw34step1 = (fun u v => extraRaw34step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw34step0 extraPermutation62 hz
    injectiveMoment H extraRaw34step1 = injectiveMoment H extraRaw34step2 := by
      have heq : extraRaw34step2 = (fun u v => extraRaw34step1 (extraPermutation55 u) (extraPermutation10 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw34step1 extraPermutation55 extraPermutation10
    _ = injectiveMoment H node2711 := by rfl

def extraRaw35 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![2, -2], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw35step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![2, -2], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw35step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem extraCanonical35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw35 = injectiveMoment H node232 := by
  calc
    injectiveMoment H extraRaw35 = injectiveMoment H extraRaw35step0 := by
      have hz : ∀ j, extraRaw35 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw35step0 = (fun u v => extraRaw35 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw35 extraPermutation62 hz
    injectiveMoment H extraRaw35step0 = injectiveMoment H extraRaw35step1 := by
      have heq : extraRaw35step1 = (fun u v => extraRaw35step0 (extraPermutation34 u) (extraPermutation1 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw35step0 extraPermutation34 extraPermutation1
    _ = injectiveMoment H node232 := by rfl

def extraRaw36 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw36step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem extraCanonical36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw36 = injectiveMoment H node545 := by
  calc
    injectiveMoment H extraRaw36 = injectiveMoment H extraRaw36step0 := by
      have hz : ∀ j, extraRaw36 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw36step0 = (fun u v => extraRaw36 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw36 extraPermutation62 hz
    _ = injectiveMoment H node545 := by rfl

def extraRaw37 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw37step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw37step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def extraRaw37step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0]]

def extraRaw37step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw37 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw37 = injectiveMoment H extraRaw37step0 := by
      have hz : ∀ j, extraRaw37 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw37step0 = (fun u v => extraRaw37 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw37 extraPermutation67 hz
    injectiveMoment H extraRaw37step0 = injectiveMoment H extraRaw37step1 := by
      have hz : ∀ j, extraRaw37step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw37step1 = (fun u v => extraRaw37step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw37step0 extraPermutation49 hz
    injectiveMoment H extraRaw37step1 = injectiveMoment H extraRaw37step2 := by
      have hz : ∀ j, extraRaw37step1 (extraPermutation20 0) j = 0 := by decide +kernel
      have heq : extraRaw37step2 = (fun u v => extraRaw37step1 (extraPermutation20 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw37step1 extraPermutation20 hz
    injectiveMoment H extraRaw37step2 = injectiveMoment H extraRaw37step3 := by
      have hz : ∀ j, extraRaw37step2 (extraPermutation6 0) j = 0 := by decide +kernel
      have heq : extraRaw37step3 = (fun u v => extraRaw37step2 (extraPermutation6 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw37step2 extraPermutation6 hz
    _ = injectiveMoment H node5 := by rfl

def extraRaw38 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw38step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw38step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

theorem extraCanonical38 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw38 = injectiveMoment H node1153 := by
  calc
    injectiveMoment H extraRaw38 = injectiveMoment H extraRaw38step0 := by
      have hz : ∀ j, extraRaw38 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw38step0 = (fun u v => extraRaw38 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw38 extraPermutation62 hz
    injectiveMoment H extraRaw38step0 = injectiveMoment H extraRaw38step1 := by
      have heq : extraRaw38step1 = (fun u v => extraRaw38step0 (extraPermutation32 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw38step0 extraPermutation32 extraPermutation2
    _ = injectiveMoment H node1153 := by rfl

def extraRaw39 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw39step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw39step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical39 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw39 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H extraRaw39 = injectiveMoment H extraRaw39step0 := by
      have hz : ∀ j, extraRaw39 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw39step0 = (fun u v => extraRaw39 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw39 extraPermutation62 hz
    injectiveMoment H extraRaw39step0 = injectiveMoment H extraRaw39step1 := by
      have heq : extraRaw39step1 = (fun u v => extraRaw39step0 (extraPermutation36 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw39step0 extraPermutation36 extraPermutation4
    _ = injectiveMoment H node1291 := by rfl

def extraRaw40 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw40step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw40step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw40step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical40 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw40 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw40 = injectiveMoment H extraRaw40step0 := by
      have heq : extraRaw40step0 = -extraRaw40 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw40).symm
    injectiveMoment H extraRaw40step0 = injectiveMoment H extraRaw40step1 := by
      have hz : ∀ j, extraRaw40step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw40step1 = (fun u v => extraRaw40step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw40step0 extraPermutation62 hz
    injectiveMoment H extraRaw40step1 = injectiveMoment H extraRaw40step2 := by
      have heq : extraRaw40step2 = (fun u v => extraRaw40step1 (extraPermutation36 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw40step1 extraPermutation36 extraPermutation3
    _ = injectiveMoment H node1151 := by rfl

def extraRaw41 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw41step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw41step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw41step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw41step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem extraCanonical41 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw41 = injectiveMoment H node287 := by
  calc
    injectiveMoment H extraRaw41 = injectiveMoment H extraRaw41step0 := by
      have heq : extraRaw41step0 = -extraRaw41 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw41).symm
    injectiveMoment H extraRaw41step0 = injectiveMoment H extraRaw41step1 := by
      have hz : ∀ j, extraRaw41step0 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw41step1 = (fun u v => extraRaw41step0 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw41step0 extraPermutation63 hz
    injectiveMoment H extraRaw41step1 = injectiveMoment H extraRaw41step2 := by
      have hz : ∀ j, extraRaw41step1 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw41step2 = (fun u v => extraRaw41step1 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw41step1 extraPermutation39 hz
    injectiveMoment H extraRaw41step2 = injectiveMoment H extraRaw41step3 := by
      have heq : extraRaw41step3 = (fun u v => extraRaw41step2 (extraPermutation11 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw41step2 extraPermutation11 extraPermutation5
    _ = injectiveMoment H node287 := by rfl

def extraRaw42 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw42step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw42step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem extraCanonical42 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw42 = injectiveMoment H node2238 := by
  calc
    injectiveMoment H extraRaw42 = injectiveMoment H extraRaw42step0 := by
      have hz : ∀ j, extraRaw42 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw42step0 = (fun u v => extraRaw42 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw42 extraPermutation62 hz
    injectiveMoment H extraRaw42step0 = injectiveMoment H extraRaw42step1 := by
      have heq : extraRaw42step1 = (fun u v => extraRaw42step0 (extraPermutation29 u) (extraPermutation10 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw42step0 extraPermutation29 extraPermutation10
    _ = injectiveMoment H node2238 := by rfl

def extraRaw43 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw43step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw43step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw43step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem extraCanonical43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw43 = injectiveMoment H node232 := by
  calc
    injectiveMoment H extraRaw43 = injectiveMoment H extraRaw43step0 := by
      have hz : ∀ j, extraRaw43 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw43step0 = (fun u v => extraRaw43 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw43 extraPermutation62 hz
    injectiveMoment H extraRaw43step0 = injectiveMoment H extraRaw43step1 := by
      have hz : ∀ j, extraRaw43step0 j (extraPermutation2 0) = 0 := by decide +kernel
      have heq : extraRaw43step1 = (fun u v => extraRaw43step0 u (extraPermutation2 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw43step0 extraPermutation2 hz
    injectiveMoment H extraRaw43step1 = injectiveMoment H extraRaw43step2 := by
      have heq : extraRaw43step2 = (fun u v => extraRaw43step1 (extraPermutation34 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw43step1 extraPermutation34 extraPermutation0
    _ = injectiveMoment H node232 := by rfl

def extraRaw44 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw44step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw44step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def extraRaw44step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def extraRaw44step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem extraCanonical44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw44 = injectiveMoment H node11 := by
  calc
    injectiveMoment H extraRaw44 = injectiveMoment H extraRaw44step0 := by
      have hz : ∀ j, extraRaw44 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw44step0 = (fun u v => extraRaw44 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw44 extraPermutation67 hz
    injectiveMoment H extraRaw44step0 = injectiveMoment H extraRaw44step1 := by
      have hz : ∀ j, extraRaw44step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw44step1 = (fun u v => extraRaw44step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw44step0 extraPermutation49 hz
    injectiveMoment H extraRaw44step1 = injectiveMoment H extraRaw44step2 := by
      have hz : ∀ j, extraRaw44step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw44step2 = (fun u v => extraRaw44step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw44step1 extraPermutation15 hz
    injectiveMoment H extraRaw44step2 = injectiveMoment H extraRaw44step3 := by
      have heq : extraRaw44step3 = (fun u v => extraRaw44step2 (extraPermutation4 u) (extraPermutation1 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw44step2 extraPermutation4 extraPermutation1
    _ = injectiveMoment H node11 := by rfl

def extraRaw45 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw45step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw45step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem extraCanonical45 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw45 = injectiveMoment H node667 := by
  calc
    injectiveMoment H extraRaw45 = injectiveMoment H extraRaw45step0 := by
      have hz : ∀ j, extraRaw45 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw45step0 = (fun u v => extraRaw45 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw45 extraPermutation62 hz
    injectiveMoment H extraRaw45step0 = injectiveMoment H extraRaw45step1 := by
      have heq : extraRaw45step1 = (fun u v => extraRaw45step0 (extraPermutation38 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw45step0 extraPermutation38 extraPermutation4
    _ = injectiveMoment H node667 := by rfl

def extraRaw46 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw46step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw46step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw46step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem extraCanonical46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw46 = injectiveMoment H node667 := by
  calc
    injectiveMoment H extraRaw46 = injectiveMoment H extraRaw46step0 := by
      have heq : extraRaw46step0 = -extraRaw46 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw46).symm
    injectiveMoment H extraRaw46step0 = injectiveMoment H extraRaw46step1 := by
      have hz : ∀ j, extraRaw46step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw46step1 = (fun u v => extraRaw46step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw46step0 extraPermutation62 hz
    injectiveMoment H extraRaw46step1 = injectiveMoment H extraRaw46step2 := by
      have heq : extraRaw46step2 = (fun u v => extraRaw46step1 (extraPermutation38 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw46step1 extraPermutation38 extraPermutation3
    _ = injectiveMoment H node667 := by rfl

def extraRaw47 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem extraCanonical47 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw47 = injectiveMoment H node11 := by
  calc
    injectiveMoment H extraRaw47 = injectiveMoment H extraRaw47step0 := by
      have hz : ∀ j, extraRaw47 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw47step0 = (fun u v => extraRaw47 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw47 extraPermutation63 hz
    injectiveMoment H extraRaw47step0 = injectiveMoment H extraRaw47step1 := by
      have hz : ∀ j, extraRaw47step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw47step1 = (fun u v => extraRaw47step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw47step0 extraPermutation39 hz
    injectiveMoment H extraRaw47step1 = injectiveMoment H extraRaw47step2 := by
      have hz : ∀ j, extraRaw47step1 (extraPermutation12 0) j = 0 := by decide +kernel
      have heq : extraRaw47step2 = (fun u v => extraRaw47step1 (extraPermutation12 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw47step1 extraPermutation12 hz
    injectiveMoment H extraRaw47step2 = injectiveMoment H extraRaw47step3 := by
      have hz : ∀ j, extraRaw47step2 j (extraPermutation4 0) = 0 := by decide +kernel
      have heq : extraRaw47step3 = (fun u v => extraRaw47step2 u (extraPermutation4 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw47step2 extraPermutation4 hz
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
