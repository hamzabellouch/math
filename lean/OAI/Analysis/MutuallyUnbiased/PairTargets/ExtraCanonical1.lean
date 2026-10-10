import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraPermutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw16 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw16step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw16step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw16step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw16step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw16step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical16 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw16 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw16 = injectiveMoment H extraRaw16step0 := by
      have hz : ∀ j, extraRaw16 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw16step0 = (fun u v => extraRaw16 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw16 extraPermutation67 hz
    injectiveMoment H extraRaw16step0 = injectiveMoment H extraRaw16step1 := by
      have hz : ∀ j, extraRaw16step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw16step1 = (fun u v => extraRaw16step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw16step0 extraPermutation49 hz
    injectiveMoment H extraRaw16step1 = injectiveMoment H extraRaw16step2 := by
      have hz : ∀ j, extraRaw16step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw16step2 = (fun u v => extraRaw16step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw16step1 extraPermutation15 hz
    injectiveMoment H extraRaw16step2 = injectiveMoment H extraRaw16step3 := by
      have hz : ∀ j, extraRaw16step2 (extraPermutation2 0) j = 0 := by decide +kernel
      have heq : extraRaw16step3 = (fun u v => extraRaw16step2 (extraPermutation2 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw16step2 extraPermutation2 hz
    injectiveMoment H extraRaw16step3 = injectiveMoment H extraRaw16step4 := by
      have heq : extraRaw16step4 = (fun u v => extraRaw16step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw16step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw17 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw17step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw17step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical17 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw17 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw17 = injectiveMoment H extraRaw17step0 := by
      have hz : ∀ j, extraRaw17 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw17step0 = (fun u v => extraRaw17 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw17 extraPermutation62 hz
    injectiveMoment H extraRaw17step0 = injectiveMoment H extraRaw17step1 := by
      have heq : extraRaw17step1 = (fun u v => extraRaw17step0 (extraPermutation36 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw17step0 extraPermutation36 extraPermutation4
    _ = injectiveMoment H node1151 := by rfl

def extraRaw18 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw18step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw18step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw18step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical18 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw18 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H extraRaw18 = injectiveMoment H extraRaw18step0 := by
      have heq : extraRaw18step0 = -extraRaw18 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw18).symm
    injectiveMoment H extraRaw18step0 = injectiveMoment H extraRaw18step1 := by
      have hz : ∀ j, extraRaw18step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw18step1 = (fun u v => extraRaw18step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw18step0 extraPermutation62 hz
    injectiveMoment H extraRaw18step1 = injectiveMoment H extraRaw18step2 := by
      have heq : extraRaw18step2 = (fun u v => extraRaw18step1 (extraPermutation36 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw18step1 extraPermutation36 extraPermutation3
    _ = injectiveMoment H node1291 := by rfl

def extraRaw19 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw19step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw19step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw19step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem extraCanonical19 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw19 = injectiveMoment H node287 := by
  calc
    injectiveMoment H extraRaw19 = injectiveMoment H extraRaw19step0 := by
      have hz : ∀ j, extraRaw19 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw19step0 = (fun u v => extraRaw19 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw19 extraPermutation63 hz
    injectiveMoment H extraRaw19step0 = injectiveMoment H extraRaw19step1 := by
      have hz : ∀ j, extraRaw19step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw19step1 = (fun u v => extraRaw19step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw19step0 extraPermutation39 hz
    injectiveMoment H extraRaw19step1 = injectiveMoment H extraRaw19step2 := by
      have heq : extraRaw19step2 = (fun u v => extraRaw19step1 (extraPermutation11 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw19step1 extraPermutation11 extraPermutation4
    _ = injectiveMoment H node287 := by rfl

def extraRaw20 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw20step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 1, 1]]

def extraRaw20step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 1, 1]]

def extraRaw20step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem extraCanonical20 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw20 = injectiveMoment H node2238 := by
  calc
    injectiveMoment H extraRaw20 = injectiveMoment H extraRaw20step0 := by
      have heq : extraRaw20step0 = -extraRaw20 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw20).symm
    injectiveMoment H extraRaw20step0 = injectiveMoment H extraRaw20step1 := by
      have hz : ∀ j, extraRaw20step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw20step1 = (fun u v => extraRaw20step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw20step0 extraPermutation62 hz
    injectiveMoment H extraRaw20step1 = injectiveMoment H extraRaw20step2 := by
      have heq : extraRaw20step2 = (fun u v => extraRaw20step1 (extraPermutation29 u) (extraPermutation16 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw20step1 extraPermutation29 extraPermutation16
    _ = injectiveMoment H node2238 := by rfl

def extraRaw21 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def extraRaw21step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw21step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw21step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def extraRaw21step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical21 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw21 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw21 = injectiveMoment H extraRaw21step0 := by
      have hz : ∀ j, extraRaw21 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw21step0 = (fun u v => extraRaw21 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw21 extraPermutation67 hz
    injectiveMoment H extraRaw21step0 = injectiveMoment H extraRaw21step1 := by
      have hz : ∀ j, extraRaw21step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw21step1 = (fun u v => extraRaw21step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw21step0 extraPermutation39 hz
    injectiveMoment H extraRaw21step1 = injectiveMoment H extraRaw21step2 := by
      have hz : ∀ j, extraRaw21step1 (extraPermutation12 0) j = 0 := by decide +kernel
      have heq : extraRaw21step2 = (fun u v => extraRaw21step1 (extraPermutation12 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw21step1 extraPermutation12 hz
    injectiveMoment H extraRaw21step2 = injectiveMoment H extraRaw21step3 := by
      have hz : ∀ j, extraRaw21step2 (extraPermutation2 0) j = 0 := by decide +kernel
      have heq : extraRaw21step3 = (fun u v => extraRaw21step2 (extraPermutation2 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw21step2 extraPermutation2 hz
    _ = injectiveMoment H node5 := by rfl

def extraRaw22 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw22step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -1, 1]]

def extraRaw22step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -1, 1]]

def extraRaw22step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem extraCanonical22 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw22 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H extraRaw22 = injectiveMoment H extraRaw22step0 := by
      have heq : extraRaw22step0 = -extraRaw22 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw22).symm
    injectiveMoment H extraRaw22step0 = injectiveMoment H extraRaw22step1 := by
      have hz : ∀ j, extraRaw22step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw22step1 = (fun u v => extraRaw22step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw22step0 extraPermutation62 hz
    injectiveMoment H extraRaw22step1 = injectiveMoment H extraRaw22step2 := by
      have heq : extraRaw22step2 = (fun u v => extraRaw22step1 (extraPermutation46 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw22step1 extraPermutation46 extraPermutation2
    _ = injectiveMoment H node1152 := by rfl

def extraRaw23 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw23step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw23step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw23step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![-1, 1]]

def extraRaw23step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw23step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical23 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw23 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw23 = injectiveMoment H extraRaw23step0 := by
      have hz : ∀ j, extraRaw23 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw23step0 = (fun u v => extraRaw23 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw23 extraPermutation67 hz
    injectiveMoment H extraRaw23step0 = injectiveMoment H extraRaw23step1 := by
      have hz : ∀ j, extraRaw23step0 (extraPermutation42 0) j = 0 := by decide +kernel
      have heq : extraRaw23step1 = (fun u v => extraRaw23step0 (extraPermutation42 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw23step0 extraPermutation42 hz
    injectiveMoment H extraRaw23step1 = injectiveMoment H extraRaw23step2 := by
      have hz : ∀ j, extraRaw23step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw23step2 = (fun u v => extraRaw23step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw23step1 extraPermutation15 hz
    injectiveMoment H extraRaw23step2 = injectiveMoment H extraRaw23step3 := by
      have hz : ∀ j, extraRaw23step2 (extraPermutation4 0) j = 0 := by decide +kernel
      have heq : extraRaw23step3 = (fun u v => extraRaw23step2 (extraPermutation4 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw23step2 extraPermutation4 hz
    injectiveMoment H extraRaw23step3 = injectiveMoment H extraRaw23step4 := by
      have heq : extraRaw23step4 = (fun u v => extraRaw23step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw23step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw24 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]

def extraRaw24step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]

def extraRaw24step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1]]

def extraRaw24step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem extraCanonical24 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw24 = injectiveMoment H node283 := by
  calc
    injectiveMoment H extraRaw24 = injectiveMoment H extraRaw24step0 := by
      have hz : ∀ j, extraRaw24 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw24step0 = (fun u v => extraRaw24 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw24 extraPermutation63 hz
    injectiveMoment H extraRaw24step0 = injectiveMoment H extraRaw24step1 := by
      have hz : ∀ j, extraRaw24step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw24step1 = (fun u v => extraRaw24step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw24step0 extraPermutation39 hz
    injectiveMoment H extraRaw24step1 = injectiveMoment H extraRaw24step2 := by
      have heq : extraRaw24step2 = (fun u v => extraRaw24step1 (extraPermutation9 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw24step1 extraPermutation9 extraPermutation4
    _ = injectiveMoment H node283 := by rfl

def extraRaw25 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1]]

def extraRaw25step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw25step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw25step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw25 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw25 = injectiveMoment H extraRaw25step0 := by
      have heq : extraRaw25step0 = -extraRaw25 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw25).symm
    injectiveMoment H extraRaw25step0 = injectiveMoment H extraRaw25step1 := by
      have hz : ∀ j, extraRaw25step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw25step1 = (fun u v => extraRaw25step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw25step0 extraPermutation62 hz
    injectiveMoment H extraRaw25step1 = injectiveMoment H extraRaw25step2 := by
      have heq : extraRaw25step2 = (fun u v => extraRaw25step1 (extraPermutation25 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw25step1 extraPermutation25 extraPermutation3
    _ = injectiveMoment H node1151 := by rfl

def extraRaw26 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw26step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw26step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem extraCanonical26 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw26 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H extraRaw26 = injectiveMoment H extraRaw26step0 := by
      have hz : ∀ j, extraRaw26 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw26step0 = (fun u v => extraRaw26 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw26 extraPermutation62 hz
    injectiveMoment H extraRaw26step0 = injectiveMoment H extraRaw26step1 := by
      have heq : extraRaw26step1 = (fun u v => extraRaw26step0 (extraPermutation45 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw26step0 extraPermutation45 extraPermutation5
    _ = injectiveMoment H node1294 := by rfl

def extraRaw27 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def extraRaw27step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def extraRaw27step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def extraRaw27step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem extraCanonical27 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw27 = injectiveMoment H node2711 := by
  calc
    injectiveMoment H extraRaw27 = injectiveMoment H extraRaw27step0 := by
      have heq : extraRaw27step0 = -extraRaw27 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw27).symm
    injectiveMoment H extraRaw27step0 = injectiveMoment H extraRaw27step1 := by
      have hz : ∀ j, extraRaw27step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw27step1 = (fun u v => extraRaw27step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw27step0 extraPermutation62 hz
    injectiveMoment H extraRaw27step1 = injectiveMoment H extraRaw27step2 := by
      have heq : extraRaw27step2 = (fun u v => extraRaw27step1 (extraPermutation48 u) (extraPermutation10 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw27step1 extraPermutation48 extraPermutation10
    _ = injectiveMoment H node2711 := by rfl

def extraRaw28 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![1, -1]]

def extraRaw28step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw28step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw28step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def extraRaw28step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical28 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw28 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw28 = injectiveMoment H extraRaw28step0 := by
      have hz : ∀ j, extraRaw28 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw28step0 = (fun u v => extraRaw28 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw28 extraPermutation66 hz
    injectiveMoment H extraRaw28step0 = injectiveMoment H extraRaw28step1 := by
      have hz : ∀ j, extraRaw28step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw28step1 = (fun u v => extraRaw28step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw28step0 extraPermutation39 hz
    injectiveMoment H extraRaw28step1 = injectiveMoment H extraRaw28step2 := by
      have hz : ∀ j, extraRaw28step1 (extraPermutation12 0) j = 0 := by decide +kernel
      have heq : extraRaw28step2 = (fun u v => extraRaw28step1 (extraPermutation12 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw28step1 extraPermutation12 hz
    injectiveMoment H extraRaw28step2 = injectiveMoment H extraRaw28step3 := by
      have hz : ∀ j, extraRaw28step2 (extraPermutation2 0) j = 0 := by decide +kernel
      have heq : extraRaw28step3 = (fun u v => extraRaw28step2 (extraPermutation2 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw28step2 extraPermutation2 hz
    _ = injectiveMoment H node5 := by rfl

def extraRaw29 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw29step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]

def extraRaw29step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]

def extraRaw29step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem extraCanonical29 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw29 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H extraRaw29 = injectiveMoment H extraRaw29step0 := by
      have heq : extraRaw29step0 = -extraRaw29 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw29).symm
    injectiveMoment H extraRaw29step0 = injectiveMoment H extraRaw29step1 := by
      have hz : ∀ j, extraRaw29step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw29step1 = (fun u v => extraRaw29step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw29step0 extraPermutation62 hz
    injectiveMoment H extraRaw29step1 = injectiveMoment H extraRaw29step2 := by
      have heq : extraRaw29step2 = (fun u v => extraRaw29step1 (extraPermutation53 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw29step1 extraPermutation53 extraPermutation2
    _ = injectiveMoment H node1152 := by rfl

def extraRaw30 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw30step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw30step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw30step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![-1, 1]]

def extraRaw30step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw30step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical30 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw30 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw30 = injectiveMoment H extraRaw30step0 := by
      have hz : ∀ j, extraRaw30 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw30step0 = (fun u v => extraRaw30 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw30 extraPermutation66 hz
    injectiveMoment H extraRaw30step0 = injectiveMoment H extraRaw30step1 := by
      have hz : ∀ j, extraRaw30step0 (extraPermutation42 0) j = 0 := by decide +kernel
      have heq : extraRaw30step1 = (fun u v => extraRaw30step0 (extraPermutation42 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw30step0 extraPermutation42 hz
    injectiveMoment H extraRaw30step1 = injectiveMoment H extraRaw30step2 := by
      have hz : ∀ j, extraRaw30step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw30step2 = (fun u v => extraRaw30step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw30step1 extraPermutation15 hz
    injectiveMoment H extraRaw30step2 = injectiveMoment H extraRaw30step3 := by
      have hz : ∀ j, extraRaw30step2 (extraPermutation4 0) j = 0 := by decide +kernel
      have heq : extraRaw30step3 = (fun u v => extraRaw30step2 (extraPermutation4 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw30step2 extraPermutation4 hz
    injectiveMoment H extraRaw30step3 = injectiveMoment H extraRaw30step4 := by
      have heq : extraRaw30step4 = (fun u v => extraRaw30step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw30step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw31 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def extraRaw31step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def extraRaw31step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2]]

def extraRaw31step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem extraCanonical31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw31 = injectiveMoment H node283 := by
  calc
    injectiveMoment H extraRaw31 = injectiveMoment H extraRaw31step0 := by
      have hz : ∀ j, extraRaw31 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw31step0 = (fun u v => extraRaw31 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw31 extraPermutation63 hz
    injectiveMoment H extraRaw31step0 = injectiveMoment H extraRaw31step1 := by
      have hz : ∀ j, extraRaw31step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw31step1 = (fun u v => extraRaw31step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw31step0 extraPermutation39 hz
    injectiveMoment H extraRaw31step1 = injectiveMoment H extraRaw31step2 := by
      have heq : extraRaw31step2 = (fun u v => extraRaw31step1 (extraPermutation8 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw31step1 extraPermutation8 extraPermutation4
    _ = injectiveMoment H node283 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
