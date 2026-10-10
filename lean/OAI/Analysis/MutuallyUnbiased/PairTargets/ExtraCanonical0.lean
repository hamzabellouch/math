import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraPermutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def extraRaw0step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw0step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw0step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem extraCanonical0 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw0 = injectiveMoment H node856 := by
  calc
    injectiveMoment H extraRaw0 = injectiveMoment H extraRaw0step0 := by
      have heq : extraRaw0step0 = -extraRaw0 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw0).symm
    injectiveMoment H extraRaw0step0 = injectiveMoment H extraRaw0step1 := by
      have hz : ∀ j, extraRaw0step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw0step1 = (fun u v => extraRaw0step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw0step0 extraPermutation62 hz
    injectiveMoment H extraRaw0step1 = injectiveMoment H extraRaw0step2 := by
      have heq : extraRaw0step2 = (fun u v => extraRaw0step1 (extraPermutation24 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw0step1 extraPermutation24 extraPermutation5
    _ = injectiveMoment H node856 := by rfl

def extraRaw1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def extraRaw1step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw1step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw1step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem extraCanonical1 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw1 = injectiveMoment H node545 := by
  calc
    injectiveMoment H extraRaw1 = injectiveMoment H extraRaw1step0 := by
      have heq : extraRaw1step0 = -extraRaw1 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw1).symm
    injectiveMoment H extraRaw1step0 = injectiveMoment H extraRaw1step1 := by
      have hz : ∀ j, extraRaw1step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw1step1 = (fun u v => extraRaw1step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw1step0 extraPermutation62 hz
    injectiveMoment H extraRaw1step1 = injectiveMoment H extraRaw1step2 := by
      have heq : extraRaw1step2 = (fun u v => extraRaw1step1 (extraPermutation24 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw1step1 extraPermutation24 extraPermutation5
    _ = injectiveMoment H node545 := by rfl

def extraRaw2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def extraRaw2step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def extraRaw2step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw2 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw2 = injectiveMoment H extraRaw2step0 := by
      have hz : ∀ j, extraRaw2 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw2step0 = (fun u v => extraRaw2 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw2 extraPermutation66 hz
    injectiveMoment H extraRaw2step0 = injectiveMoment H extraRaw2step1 := by
      have hz : ∀ j, extraRaw2step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw2step1 = (fun u v => extraRaw2step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw2step0 extraPermutation39 hz
    _ = injectiveMoment H node65 := by rfl

def extraRaw3 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]

def extraRaw3step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 1, 1]]

def extraRaw3step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 1, 1]]

def extraRaw3step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem extraCanonical3 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw3 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw3 = injectiveMoment H extraRaw3step0 := by
      have heq : extraRaw3step0 = -extraRaw3 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw3).symm
    injectiveMoment H extraRaw3step0 = injectiveMoment H extraRaw3step1 := by
      have hz : ∀ j, extraRaw3step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw3step1 = (fun u v => extraRaw3step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw3step0 extraPermutation62 hz
    injectiveMoment H extraRaw3step1 = injectiveMoment H extraRaw3step2 := by
      have heq : extraRaw3step2 = (fun u v => extraRaw3step1 (extraPermutation26 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw3step1 extraPermutation26 extraPermutation5
    _ = injectiveMoment H node858 := by rfl

def extraRaw4 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def extraRaw4step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def extraRaw4step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw4 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw4 = injectiveMoment H extraRaw4step0 := by
      have hz : ∀ j, extraRaw4 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw4step0 = (fun u v => extraRaw4 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw4 extraPermutation67 hz
    injectiveMoment H extraRaw4step0 = injectiveMoment H extraRaw4step1 := by
      have hz : ∀ j, extraRaw4step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw4step1 = (fun u v => extraRaw4step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw4step0 extraPermutation39 hz
    _ = injectiveMoment H node65 := by rfl

def extraRaw5 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def extraRaw5step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def extraRaw5step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def extraRaw5step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem extraCanonical5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw5 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw5 = injectiveMoment H extraRaw5step0 := by
      have heq : extraRaw5step0 = -extraRaw5 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw5).symm
    injectiveMoment H extraRaw5step0 = injectiveMoment H extraRaw5step1 := by
      have hz : ∀ j, extraRaw5step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw5step1 = (fun u v => extraRaw5step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw5step0 extraPermutation62 hz
    injectiveMoment H extraRaw5step1 = injectiveMoment H extraRaw5step2 := by
      have heq : extraRaw5step2 = (fun u v => extraRaw5step1 (extraPermutation28 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw5step1 extraPermutation28 extraPermutation5
    _ = injectiveMoment H node858 := by rfl

def extraRaw6 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw6step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw6step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem extraCanonical6 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw6 = injectiveMoment H node232 := by
  calc
    injectiveMoment H extraRaw6 = injectiveMoment H extraRaw6step0 := by
      have hz : ∀ j, extraRaw6 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw6step0 = (fun u v => extraRaw6 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw6 extraPermutation62 hz
    injectiveMoment H extraRaw6step0 = injectiveMoment H extraRaw6step1 := by
      have heq : extraRaw6step1 = (fun u v => extraRaw6step0 (extraPermutation24 u) (extraPermutation1 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw6step0 extraPermutation24 extraPermutation1
    _ = injectiveMoment H node232 := by rfl

def extraRaw7 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw7step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem extraCanonical7 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw7 = injectiveMoment H node856 := by
  calc
    injectiveMoment H extraRaw7 = injectiveMoment H extraRaw7step0 := by
      have hz : ∀ j, extraRaw7 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw7step0 = (fun u v => extraRaw7 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw7 extraPermutation62 hz
    _ = injectiveMoment H node856 := by rfl

def extraRaw8 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw8step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw8step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem extraCanonical8 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw8 = injectiveMoment H node232 := by
  calc
    injectiveMoment H extraRaw8 = injectiveMoment H extraRaw8step0 := by
      have hz : ∀ j, extraRaw8 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw8step0 = (fun u v => extraRaw8 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw8 extraPermutation62 hz
    injectiveMoment H extraRaw8step0 = injectiveMoment H extraRaw8step1 := by
      have hz : ∀ j, extraRaw8step0 j (extraPermutation2 0) = 0 := by decide +kernel
      have heq : extraRaw8step1 = (fun u v => extraRaw8step0 u (extraPermutation2 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw8step0 extraPermutation2 hz
    _ = injectiveMoment H node232 := by rfl

def extraRaw9 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw9step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw9step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw9step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![-1, 1]]

def extraRaw9step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw9step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw9 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw9 = injectiveMoment H extraRaw9step0 := by
      have hz : ∀ j, extraRaw9 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw9step0 = (fun u v => extraRaw9 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw9 extraPermutation67 hz
    injectiveMoment H extraRaw9step0 = injectiveMoment H extraRaw9step1 := by
      have hz : ∀ j, extraRaw9step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw9step1 = (fun u v => extraRaw9step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw9step0 extraPermutation49 hz
    injectiveMoment H extraRaw9step1 = injectiveMoment H extraRaw9step2 := by
      have hz : ∀ j, extraRaw9step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw9step2 = (fun u v => extraRaw9step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw9step1 extraPermutation15 hz
    injectiveMoment H extraRaw9step2 = injectiveMoment H extraRaw9step3 := by
      have hz : ∀ j, extraRaw9step2 (extraPermutation4 0) j = 0 := by decide +kernel
      have heq : extraRaw9step3 = (fun u v => extraRaw9step2 (extraPermutation4 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw9step2 extraPermutation4 hz
    injectiveMoment H extraRaw9step3 = injectiveMoment H extraRaw9step4 := by
      have heq : extraRaw9step4 = (fun u v => extraRaw9step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw9step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw10 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw10step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw10step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical10 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw10 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw10 = injectiveMoment H extraRaw10step0 := by
      have hz : ∀ j, extraRaw10 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw10step0 = (fun u v => extraRaw10 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw10 extraPermutation62 hz
    injectiveMoment H extraRaw10step0 = injectiveMoment H extraRaw10step1 := by
      have heq : extraRaw10step1 = (fun u v => extraRaw10step0 (extraPermutation27 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw10step0 extraPermutation27 extraPermutation4
    _ = injectiveMoment H node1151 := by rfl

def extraRaw11 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw11step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw11step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw11step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw11 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw11 = injectiveMoment H extraRaw11step0 := by
      have heq : extraRaw11step0 = -extraRaw11 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw11).symm
    injectiveMoment H extraRaw11step0 = injectiveMoment H extraRaw11step1 := by
      have hz : ∀ j, extraRaw11step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw11step1 = (fun u v => extraRaw11step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw11step0 extraPermutation62 hz
    injectiveMoment H extraRaw11step1 = injectiveMoment H extraRaw11step2 := by
      have heq : extraRaw11step2 = (fun u v => extraRaw11step1 (extraPermutation27 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw11step1 extraPermutation27 extraPermutation3
    _ = injectiveMoment H node1151 := by rfl

def extraRaw12 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw12step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw12step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw12step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical12 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw12 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw12 = injectiveMoment H extraRaw12step0 := by
      have hz : ∀ j, extraRaw12 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw12step0 = (fun u v => extraRaw12 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw12 extraPermutation63 hz
    injectiveMoment H extraRaw12step0 = injectiveMoment H extraRaw12step1 := by
      have hz : ∀ j, extraRaw12step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw12step1 = (fun u v => extraRaw12step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw12step0 extraPermutation39 hz
    injectiveMoment H extraRaw12step1 = injectiveMoment H extraRaw12step2 := by
      have hz : ∀ j, extraRaw12step1 j (extraPermutation4 0) = 0 := by decide +kernel
      have heq : extraRaw12step2 = (fun u v => extraRaw12step1 u (extraPermutation4 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw12step1 extraPermutation4 hz
    _ = injectiveMoment H node65 := by rfl

def extraRaw13 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw13step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw13step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem extraCanonical13 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw13 = injectiveMoment H node2838 := by
  calc
    injectiveMoment H extraRaw13 = injectiveMoment H extraRaw13step0 := by
      have hz : ∀ j, extraRaw13 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw13step0 = (fun u v => extraRaw13 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw13 extraPermutation62 hz
    injectiveMoment H extraRaw13step0 = injectiveMoment H extraRaw13step1 := by
      have heq : extraRaw13step1 = (fun u v => extraRaw13step0 (extraPermutation24 u) (extraPermutation10 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw13step0 extraPermutation24 extraPermutation10
    _ = injectiveMoment H node2838 := by rfl

def extraRaw14 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw14step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw14step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw14step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0]]

def extraRaw14step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw14step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical14 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw14 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw14 = injectiveMoment H extraRaw14step0 := by
      have hz : ∀ j, extraRaw14 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw14step0 = (fun u v => extraRaw14 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw14 extraPermutation67 hz
    injectiveMoment H extraRaw14step0 = injectiveMoment H extraRaw14step1 := by
      have hz : ∀ j, extraRaw14step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw14step1 = (fun u v => extraRaw14step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw14step0 extraPermutation49 hz
    injectiveMoment H extraRaw14step1 = injectiveMoment H extraRaw14step2 := by
      have hz : ∀ j, extraRaw14step1 (extraPermutation20 0) j = 0 := by decide +kernel
      have heq : extraRaw14step2 = (fun u v => extraRaw14step1 (extraPermutation20 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw14step1 extraPermutation20 hz
    injectiveMoment H extraRaw14step2 = injectiveMoment H extraRaw14step3 := by
      have hz : ∀ j, extraRaw14step2 (extraPermutation6 0) j = 0 := by decide +kernel
      have heq : extraRaw14step3 = (fun u v => extraRaw14step2 (extraPermutation6 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw14step2 extraPermutation6 hz
    injectiveMoment H extraRaw14step3 = injectiveMoment H extraRaw14step4 := by
      have heq : extraRaw14step4 = (fun u v => extraRaw14step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw14step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw15 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw15step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw15step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

theorem extraCanonical15 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw15 = injectiveMoment H node1153 := by
  calc
    injectiveMoment H extraRaw15 = injectiveMoment H extraRaw15step0 := by
      have hz : ∀ j, extraRaw15 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw15step0 = (fun u v => extraRaw15 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw15 extraPermutation62 hz
    injectiveMoment H extraRaw15step0 = injectiveMoment H extraRaw15step1 := by
      have heq : extraRaw15step1 = (fun u v => extraRaw15step0 (extraPermutation37 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw15step0 extraPermutation37 extraPermutation2
    _ = injectiveMoment H node1153 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
