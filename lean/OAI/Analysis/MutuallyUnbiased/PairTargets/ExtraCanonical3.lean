import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraPermutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw48 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -2, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw48step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw48step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem extraCanonical48 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw48 = injectiveMoment H node2354 := by
  calc
    injectiveMoment H extraRaw48 = injectiveMoment H extraRaw48step0 := by
      have hz : ∀ j, extraRaw48 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw48step0 = (fun u v => extraRaw48 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw48 extraPermutation62 hz
    injectiveMoment H extraRaw48step0 = injectiveMoment H extraRaw48step1 := by
      have heq : extraRaw48step1 = (fun u v => extraRaw48step0 (extraPermutation24 u) (extraPermutation10 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw48step0 extraPermutation24 extraPermutation10
    _ = injectiveMoment H node2354 := by rfl

def extraRaw49 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def extraRaw49step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw49step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def extraRaw49step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical49 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw49 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw49 = injectiveMoment H extraRaw49step0 := by
      have hz : ∀ j, extraRaw49 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw49step0 = (fun u v => extraRaw49 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw49 extraPermutation67 hz
    injectiveMoment H extraRaw49step0 = injectiveMoment H extraRaw49step1 := by
      have hz : ∀ j, extraRaw49step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw49step1 = (fun u v => extraRaw49step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw49step0 extraPermutation39 hz
    injectiveMoment H extraRaw49step1 = injectiveMoment H extraRaw49step2 := by
      have heq : extraRaw49step2 = (fun u v => extraRaw49step1 (extraPermutation10 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw49step1 extraPermutation10 extraPermutation0
    _ = injectiveMoment H node65 := by rfl

def extraRaw50 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw50step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw50step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem extraCanonical50 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw50 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H extraRaw50 = injectiveMoment H extraRaw50step0 := by
      have hz : ∀ j, extraRaw50 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw50step0 = (fun u v => extraRaw50 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw50 extraPermutation62 hz
    injectiveMoment H extraRaw50step0 = injectiveMoment H extraRaw50step1 := by
      have heq : extraRaw50step1 = (fun u v => extraRaw50step0 (extraPermutation33 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw50step0 extraPermutation33 extraPermutation2
    _ = injectiveMoment H node1141 := by rfl

def extraRaw51 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw51step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw51step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw51step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw51step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw51step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical51 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw51 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw51 = injectiveMoment H extraRaw51step0 := by
      have hz : ∀ j, extraRaw51 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw51step0 = (fun u v => extraRaw51 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw51 extraPermutation67 hz
    injectiveMoment H extraRaw51step0 = injectiveMoment H extraRaw51step1 := by
      have hz : ∀ j, extraRaw51step0 (extraPermutation42 0) j = 0 := by decide +kernel
      have heq : extraRaw51step1 = (fun u v => extraRaw51step0 (extraPermutation42 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw51step0 extraPermutation42 hz
    injectiveMoment H extraRaw51step1 = injectiveMoment H extraRaw51step2 := by
      have hz : ∀ j, extraRaw51step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw51step2 = (fun u v => extraRaw51step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw51step1 extraPermutation15 hz
    injectiveMoment H extraRaw51step2 = injectiveMoment H extraRaw51step3 := by
      have hz : ∀ j, extraRaw51step2 (extraPermutation2 0) j = 0 := by decide +kernel
      have heq : extraRaw51step3 = (fun u v => extraRaw51step2 (extraPermutation2 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw51step2 extraPermutation2 hz
    injectiveMoment H extraRaw51step3 = injectiveMoment H extraRaw51step4 := by
      have heq : extraRaw51step4 = (fun u v => extraRaw51step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw51step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw52 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]

def extraRaw52step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, 0, 1]]

def extraRaw52step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, 0, 1]]

def extraRaw52step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, -1, 2], ![-1, 0, 1]]

def extraRaw52step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem extraCanonical52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw52 = injectiveMoment H node284 := by
  calc
    injectiveMoment H extraRaw52 = injectiveMoment H extraRaw52step0 := by
      have heq : extraRaw52step0 = -extraRaw52 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw52).symm
    injectiveMoment H extraRaw52step0 = injectiveMoment H extraRaw52step1 := by
      have hz : ∀ j, extraRaw52step0 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw52step1 = (fun u v => extraRaw52step0 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw52step0 extraPermutation63 hz
    injectiveMoment H extraRaw52step1 = injectiveMoment H extraRaw52step2 := by
      have hz : ∀ j, extraRaw52step1 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw52step2 = (fun u v => extraRaw52step1 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw52step1 extraPermutation39 hz
    injectiveMoment H extraRaw52step2 = injectiveMoment H extraRaw52step3 := by
      have heq : extraRaw52step3 = (fun u v => extraRaw52step2 (extraPermutation18 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw52step2 extraPermutation18 extraPermutation4
    _ = injectiveMoment H node284 := by rfl

def extraRaw53 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1]]

def extraRaw53step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw53step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw53step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical53 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw53 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw53 = injectiveMoment H extraRaw53step0 := by
      have heq : extraRaw53step0 = -extraRaw53 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw53).symm
    injectiveMoment H extraRaw53step0 = injectiveMoment H extraRaw53step1 := by
      have hz : ∀ j, extraRaw53step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw53step1 = (fun u v => extraRaw53step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw53step0 extraPermutation62 hz
    injectiveMoment H extraRaw53step1 = injectiveMoment H extraRaw53step2 := by
      have heq : extraRaw53step2 = (fun u v => extraRaw53step1 (extraPermutation35 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw53step1 extraPermutation35 extraPermutation3
    _ = injectiveMoment H node1151 := by rfl

def extraRaw54 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw54step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem extraCanonical54 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw54 = injectiveMoment H node711 := by
  calc
    injectiveMoment H extraRaw54 = injectiveMoment H extraRaw54step0 := by
      have hz : ∀ j, extraRaw54 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw54step0 = (fun u v => extraRaw54 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw54 extraPermutation62 hz
    _ = injectiveMoment H node711 := by rfl

def extraRaw55 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def extraRaw55step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def extraRaw55step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem extraCanonical55 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw55 = injectiveMoment H node2204 := by
  calc
    injectiveMoment H extraRaw55 = injectiveMoment H extraRaw55step0 := by
      have hz : ∀ j, extraRaw55 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw55step0 = (fun u v => extraRaw55 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw55 extraPermutation62 hz
    injectiveMoment H extraRaw55step0 = injectiveMoment H extraRaw55step1 := by
      have heq : extraRaw55step1 = (fun u v => extraRaw55step0 (extraPermutation30 u) (extraPermutation10 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw55step0 extraPermutation30 extraPermutation10
    _ = injectiveMoment H node2204 := by rfl

def extraRaw56 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![1, -1]]

def extraRaw56step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw56step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def extraRaw56step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical56 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw56 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw56 = injectiveMoment H extraRaw56step0 := by
      have hz : ∀ j, extraRaw56 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw56step0 = (fun u v => extraRaw56 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw56 extraPermutation66 hz
    injectiveMoment H extraRaw56step0 = injectiveMoment H extraRaw56step1 := by
      have hz : ∀ j, extraRaw56step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw56step1 = (fun u v => extraRaw56step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw56step0 extraPermutation39 hz
    injectiveMoment H extraRaw56step1 = injectiveMoment H extraRaw56step2 := by
      have heq : extraRaw56step2 = (fun u v => extraRaw56step1 (extraPermutation10 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw56step1 extraPermutation10 extraPermutation0
    _ = injectiveMoment H node65 := by rfl

def extraRaw57 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw57step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw57step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem extraCanonical57 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw57 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H extraRaw57 = injectiveMoment H extraRaw57step0 := by
      have hz : ∀ j, extraRaw57 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw57step0 = (fun u v => extraRaw57 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw57 extraPermutation62 hz
    injectiveMoment H extraRaw57step0 = injectiveMoment H extraRaw57step1 := by
      have heq : extraRaw57step1 = (fun u v => extraRaw57step0 (extraPermutation31 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw57step0 extraPermutation31 extraPermutation2
    _ = injectiveMoment H node1141 := by rfl

def extraRaw58 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw58step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw58step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw58step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw58step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw58step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical58 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw58 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw58 = injectiveMoment H extraRaw58step0 := by
      have hz : ∀ j, extraRaw58 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw58step0 = (fun u v => extraRaw58 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw58 extraPermutation66 hz
    injectiveMoment H extraRaw58step0 = injectiveMoment H extraRaw58step1 := by
      have hz : ∀ j, extraRaw58step0 (extraPermutation42 0) j = 0 := by decide +kernel
      have heq : extraRaw58step1 = (fun u v => extraRaw58step0 (extraPermutation42 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw58step0 extraPermutation42 hz
    injectiveMoment H extraRaw58step1 = injectiveMoment H extraRaw58step2 := by
      have hz : ∀ j, extraRaw58step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw58step2 = (fun u v => extraRaw58step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw58step1 extraPermutation15 hz
    injectiveMoment H extraRaw58step2 = injectiveMoment H extraRaw58step3 := by
      have hz : ∀ j, extraRaw58step2 (extraPermutation2 0) j = 0 := by decide +kernel
      have heq : extraRaw58step3 = (fun u v => extraRaw58step2 (extraPermutation2 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw58step2 extraPermutation2 hz
    injectiveMoment H extraRaw58step3 = injectiveMoment H extraRaw58step4 := by
      have heq : extraRaw58step4 = (fun u v => extraRaw58step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw58step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw59 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def extraRaw59step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]

def extraRaw59step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]

def extraRaw59step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]

def extraRaw59step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem extraCanonical59 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw59 = injectiveMoment H node284 := by
  calc
    injectiveMoment H extraRaw59 = injectiveMoment H extraRaw59step0 := by
      have heq : extraRaw59step0 = -extraRaw59 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw59).symm
    injectiveMoment H extraRaw59step0 = injectiveMoment H extraRaw59step1 := by
      have hz : ∀ j, extraRaw59step0 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw59step1 = (fun u v => extraRaw59step0 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw59step0 extraPermutation63 hz
    injectiveMoment H extraRaw59step1 = injectiveMoment H extraRaw59step2 := by
      have hz : ∀ j, extraRaw59step1 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw59step2 = (fun u v => extraRaw59step1 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw59step1 extraPermutation39 hz
    injectiveMoment H extraRaw59step2 = injectiveMoment H extraRaw59step3 := by
      have heq : extraRaw59step3 = (fun u v => extraRaw59step2 (extraPermutation22 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw59step2 extraPermutation22 extraPermutation4
    _ = injectiveMoment H node284 := by rfl

def extraRaw60 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]

def extraRaw60step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw60step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw60step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical60 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw60 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw60 = injectiveMoment H extraRaw60step0 := by
      have heq : extraRaw60step0 = -extraRaw60 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw60).symm
    injectiveMoment H extraRaw60step0 = injectiveMoment H extraRaw60step1 := by
      have hz : ∀ j, extraRaw60step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw60step1 = (fun u v => extraRaw60step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw60step0 extraPermutation62 hz
    injectiveMoment H extraRaw60step1 = injectiveMoment H extraRaw60step2 := by
      have heq : extraRaw60step2 = (fun u v => extraRaw60step1 (extraPermutation34 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw60step1 extraPermutation34 extraPermutation3
    _ = injectiveMoment H node1151 := by rfl

def extraRaw61 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw61step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw61step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem extraCanonical61 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw61 = injectiveMoment H node711 := by
  calc
    injectiveMoment H extraRaw61 = injectiveMoment H extraRaw61step0 := by
      have hz : ∀ j, extraRaw61 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw61step0 = (fun u v => extraRaw61 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw61 extraPermutation62 hz
    injectiveMoment H extraRaw61step0 = injectiveMoment H extraRaw61step1 := by
      have heq : extraRaw61step1 = (fun u v => extraRaw61step0 (extraPermutation25 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw61step0 extraPermutation25 extraPermutation2
    _ = injectiveMoment H node711 := by rfl

def extraRaw62 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def extraRaw62step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def extraRaw62step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem extraCanonical62 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw62 = injectiveMoment H node2204 := by
  calc
    injectiveMoment H extraRaw62 = injectiveMoment H extraRaw62step0 := by
      have hz : ∀ j, extraRaw62 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw62step0 = (fun u v => extraRaw62 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw62 extraPermutation62 hz
    injectiveMoment H extraRaw62step0 = injectiveMoment H extraRaw62step1 := by
      have heq : extraRaw62step1 = (fun u v => extraRaw62step0 (extraPermutation29 u) (extraPermutation10 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw62step0 extraPermutation29 extraPermutation10
    _ = injectiveMoment H node2204 := by rfl

def extraRaw63 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![-1, 1]]

def extraRaw63step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-2, 2], ![-1, 1]]

def extraRaw63step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-2, 2], ![-1, 1]]

def extraRaw63step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem extraCanonical63 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw63 = injectiveMoment H node46 := by
  calc
    injectiveMoment H extraRaw63 = injectiveMoment H extraRaw63step0 := by
      have hz : ∀ j, extraRaw63 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw63step0 = (fun u v => extraRaw63 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw63 extraPermutation63 hz
    injectiveMoment H extraRaw63step0 = injectiveMoment H extraRaw63step1 := by
      have hz : ∀ j, extraRaw63step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw63step1 = (fun u v => extraRaw63step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw63step0 extraPermutation39 hz
    injectiveMoment H extraRaw63step1 = injectiveMoment H extraRaw63step2 := by
      have heq : extraRaw63step2 = (fun u v => extraRaw63step1 (extraPermutation19 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw63step1 extraPermutation19 extraPermutation0
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
