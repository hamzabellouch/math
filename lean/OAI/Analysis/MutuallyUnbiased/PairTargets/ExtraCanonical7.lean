import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraPermutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2]]

def extraRaw112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]

def extraRaw112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]

def extraRaw112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem extraCanonical112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw112 = injectiveMoment H node659 := by
  calc
    injectiveMoment H extraRaw112 = injectiveMoment H extraRaw112step0 := by
      have heq : extraRaw112step0 = -extraRaw112 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw112).symm
    injectiveMoment H extraRaw112step0 = injectiveMoment H extraRaw112step1 := by
      have hz : ∀ j, extraRaw112step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw112step1 = (fun u v => extraRaw112step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw112step0 extraPermutation62 hz
    injectiveMoment H extraRaw112step1 = injectiveMoment H extraRaw112step2 := by
      have heq : extraRaw112step2 = (fun u v => extraRaw112step1 (extraPermutation54 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw112step1 extraPermutation54 extraPermutation4
    _ = injectiveMoment H node659 := by rfl

def extraRaw113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]

def extraRaw113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]

def extraRaw113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem extraCanonical113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw113 = injectiveMoment H node659 := by
  calc
    injectiveMoment H extraRaw113 = injectiveMoment H extraRaw113step0 := by
      have hz : ∀ j, extraRaw113 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw113step0 = (fun u v => extraRaw113 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw113 extraPermutation62 hz
    injectiveMoment H extraRaw113step0 = injectiveMoment H extraRaw113step1 := by
      have heq : extraRaw113step1 = (fun u v => extraRaw113step0 (extraPermutation54 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw113step0 extraPermutation54 extraPermutation3
    _ = injectiveMoment H node659 := by rfl

def extraRaw114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]

def extraRaw114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw114step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw114 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw114 = injectiveMoment H extraRaw114step0 := by
      have hz : ∀ j, extraRaw114 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw114step0 = (fun u v => extraRaw114 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw114 extraPermutation67 hz
    injectiveMoment H extraRaw114step0 = injectiveMoment H extraRaw114step1 := by
      have hz : ∀ j, extraRaw114step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw114step1 = (fun u v => extraRaw114step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw114step0 extraPermutation39 hz
    injectiveMoment H extraRaw114step1 = injectiveMoment H extraRaw114step2 := by
      have hz : ∀ j, extraRaw114step1 j (extraPermutation4 0) = 0 := by decide +kernel
      have heq : extraRaw114step2 = (fun u v => extraRaw114step1 u (extraPermutation4 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw114step1 extraPermutation4 hz
    _ = injectiveMoment H node65 := by rfl

def extraRaw115 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1], ![0, 2, 0, -2]]

def extraRaw115step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![1, 1, -1, -1], ![0, 2, 0, -2]]

def extraRaw115step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem extraCanonical115 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw115 = injectiveMoment H node2839 := by
  calc
    injectiveMoment H extraRaw115 = injectiveMoment H extraRaw115step0 := by
      have hz : ∀ j, extraRaw115 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw115step0 = (fun u v => extraRaw115 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw115 extraPermutation62 hz
    injectiveMoment H extraRaw115step0 = injectiveMoment H extraRaw115step1 := by
      have heq : extraRaw115step1 = (fun u v => extraRaw115step0 (extraPermutation28 u) (extraPermutation10 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw115step0 extraPermutation28 extraPermutation10
    _ = injectiveMoment H node2839 := by rfl

def extraRaw116 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![0, 0]]

def extraRaw116step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2], ![0, 0]]

def extraRaw116step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2]]

def extraRaw116step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![-2, 2]]

def extraRaw116step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw116step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem extraCanonical116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw116 = injectiveMoment H node4 := by
  calc
    injectiveMoment H extraRaw116 = injectiveMoment H extraRaw116step0 := by
      have hz : ∀ j, extraRaw116 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw116step0 = (fun u v => extraRaw116 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw116 extraPermutation67 hz
    injectiveMoment H extraRaw116step0 = injectiveMoment H extraRaw116step1 := by
      have hz : ∀ j, extraRaw116step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw116step1 = (fun u v => extraRaw116step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw116step0 extraPermutation49 hz
    injectiveMoment H extraRaw116step1 = injectiveMoment H extraRaw116step2 := by
      have hz : ∀ j, extraRaw116step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw116step2 = (fun u v => extraRaw116step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw116step1 extraPermutation15 hz
    injectiveMoment H extraRaw116step2 = injectiveMoment H extraRaw116step3 := by
      have hz : ∀ j, extraRaw116step2 (extraPermutation4 0) j = 0 := by decide +kernel
      have heq : extraRaw116step3 = (fun u v => extraRaw116step2 (extraPermutation4 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw116step2 extraPermutation4 hz
    injectiveMoment H extraRaw116step3 = injectiveMoment H extraRaw116step4 := by
      have heq : extraRaw116step4 = (fun u v => extraRaw116step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw116step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node4 := by rfl

def extraRaw117 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-3, 3], ![-1, 1], ![-1, 1]]

def extraRaw117step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

theorem extraCanonical117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw117 = injectiveMoment H node381 := by
  calc
    injectiveMoment H extraRaw117 = injectiveMoment H extraRaw117step0 := by
      have heq : extraRaw117step0 = (fun u v => extraRaw117 (extraPermutation65 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw117 extraPermutation65 extraPermutation0
    _ = injectiveMoment H node381 := by rfl

def extraRaw118 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem extraCanonical118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw118 = injectiveMoment H node1873 := by
  calc
    injectiveMoment H extraRaw118 = injectiveMoment H extraRaw118step0 := by
      have heq : extraRaw118step0 = (fun u v => extraRaw118 (extraPermutation56 u) (extraPermutation7 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw118 extraPermutation56 extraPermutation7
    _ = injectiveMoment H node1873 := by rfl

def extraRaw119 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0], ![0, 0]]

def extraRaw119step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]

def extraRaw119step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def extraRaw119step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def extraRaw119step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem extraCanonical119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw119 = injectiveMoment H node4 := by
  calc
    injectiveMoment H extraRaw119 = injectiveMoment H extraRaw119step0 := by
      have hz : ∀ j, extraRaw119 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw119step0 = (fun u v => extraRaw119 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw119 extraPermutation67 hz
    injectiveMoment H extraRaw119step0 = injectiveMoment H extraRaw119step1 := by
      have hz : ∀ j, extraRaw119step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw119step1 = (fun u v => extraRaw119step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw119step0 extraPermutation49 hz
    injectiveMoment H extraRaw119step1 = injectiveMoment H extraRaw119step2 := by
      have hz : ∀ j, extraRaw119step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw119step2 = (fun u v => extraRaw119step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw119step1 extraPermutation15 hz
    injectiveMoment H extraRaw119step2 = injectiveMoment H extraRaw119step3 := by
      have hz : ∀ j, extraRaw119step2 (extraPermutation4 0) j = 0 := by decide +kernel
      have heq : extraRaw119step3 = (fun u v => extraRaw119step2 (extraPermutation4 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw119step2 extraPermutation4 hz
    _ = injectiveMoment H node4 := by rfl

def extraRaw120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0]]

def extraRaw120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0]]

def extraRaw120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]

def extraRaw120step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, -2, 2]]

def extraRaw120step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2]]

def extraRaw120step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw120step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem extraCanonical120 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw120 = injectiveMoment H node4 := by
  calc
    injectiveMoment H extraRaw120 = injectiveMoment H extraRaw120step0 := by
      have hz : ∀ j, extraRaw120 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw120step0 = (fun u v => extraRaw120 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw120 extraPermutation67 hz
    injectiveMoment H extraRaw120step0 = injectiveMoment H extraRaw120step1 := by
      have hz : ∀ j, extraRaw120step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw120step1 = (fun u v => extraRaw120step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw120step0 extraPermutation49 hz
    injectiveMoment H extraRaw120step1 = injectiveMoment H extraRaw120step2 := by
      have hz : ∀ j, extraRaw120step1 (extraPermutation15 0) j = 0 := by decide +kernel
      have heq : extraRaw120step2 = (fun u v => extraRaw120step1 (extraPermutation15 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw120step1 extraPermutation15 hz
    injectiveMoment H extraRaw120step2 = injectiveMoment H extraRaw120step3 := by
      have hz : ∀ j, extraRaw120step2 (extraPermutation4 0) j = 0 := by decide +kernel
      have heq : extraRaw120step3 = (fun u v => extraRaw120step2 (extraPermutation4 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw120step2 extraPermutation4 hz
    injectiveMoment H extraRaw120step3 = injectiveMoment H extraRaw120step4 := by
      have hz : ∀ j, extraRaw120step3 j (extraPermutation2 0) = 0 := by decide +kernel
      have heq : extraRaw120step4 = (fun u v => extraRaw120step3 u (extraPermutation2 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw120step3 extraPermutation2 hz
    injectiveMoment H extraRaw120step4 = injectiveMoment H extraRaw120step5 := by
      have heq : extraRaw120step5 = (fun u v => extraRaw120step4 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw120step4 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node4 := by rfl

def extraRaw121 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw121step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem extraCanonical121 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw121 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H extraRaw121 = injectiveMoment H extraRaw121step0 := by
      have heq : extraRaw121step0 = (fun u v => extraRaw121 (extraPermutation59 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw121 extraPermutation59 extraPermutation0
    _ = injectiveMoment H node1323 := by rfl

def extraRaw122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem extraCanonical122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw122 = injectiveMoment H node2304 := by
  calc
    injectiveMoment H extraRaw122 = injectiveMoment H extraRaw122step0 := by
      have heq : extraRaw122step0 = (fun u v => extraRaw122 (extraPermutation59 u) (extraPermutation6 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw122 extraPermutation59 extraPermutation6
    _ = injectiveMoment H node2304 := by rfl

def extraRaw123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem extraCanonical123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw123 = injectiveMoment H node2304 := by
  calc
    injectiveMoment H extraRaw123 = injectiveMoment H extraRaw123step0 := by
      have heq : extraRaw123step0 = (fun u v => extraRaw123 (extraPermutation65 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw123 extraPermutation65 extraPermutation4
    _ = injectiveMoment H node2304 := by rfl

def extraRaw124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw124step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw124step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem extraCanonical124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw124 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H extraRaw124 = injectiveMoment H extraRaw124step0 := by
      have hz : ∀ j, extraRaw124 j (extraPermutation4 0) = 0 := by decide +kernel
      have heq : extraRaw124step0 = (fun u v => extraRaw124 u (extraPermutation4 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw124 extraPermutation4 hz
    injectiveMoment H extraRaw124step0 = injectiveMoment H extraRaw124step1 := by
      have heq : extraRaw124step1 = (fun u v => extraRaw124step0 (extraPermutation64 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw124step0 extraPermutation64 extraPermutation0
    _ = injectiveMoment H node1323 := by rfl

def extraRaw125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem extraCanonical125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw125 = injectiveMoment H node1873 := by
  calc
    injectiveMoment H extraRaw125 = injectiveMoment H extraRaw125step0 := by
      have heq : extraRaw125step0 = (fun u v => extraRaw125 (extraPermutation65 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw125 extraPermutation65 extraPermutation4
    _ = injectiveMoment H node1873 := by rfl

def extraRaw126 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, -2, 1, 2], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def extraRaw126step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

theorem extraCanonical126 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw126 = injectiveMoment H node3317 := by
  calc
    injectiveMoment H extraRaw126 = injectiveMoment H extraRaw126step0 := by
      have heq : extraRaw126step0 = (fun u v => extraRaw126 (extraPermutation65 u) (extraPermutation13 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw126 extraPermutation65 extraPermutation13
    _ = injectiveMoment H node3317 := by rfl

def extraRaw127 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw127step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw127step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0], ![0, 0]]

def extraRaw127step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0]]

def extraRaw127step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw127step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem extraCanonical127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw127 = injectiveMoment H node4 := by
  calc
    injectiveMoment H extraRaw127 = injectiveMoment H extraRaw127step0 := by
      have hz : ∀ j, extraRaw127 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw127step0 = (fun u v => extraRaw127 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw127 extraPermutation67 hz
    injectiveMoment H extraRaw127step0 = injectiveMoment H extraRaw127step1 := by
      have hz : ∀ j, extraRaw127step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw127step1 = (fun u v => extraRaw127step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw127step0 extraPermutation49 hz
    injectiveMoment H extraRaw127step1 = injectiveMoment H extraRaw127step2 := by
      have hz : ∀ j, extraRaw127step1 (extraPermutation20 0) j = 0 := by decide +kernel
      have heq : extraRaw127step2 = (fun u v => extraRaw127step1 (extraPermutation20 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw127step1 extraPermutation20 hz
    injectiveMoment H extraRaw127step2 = injectiveMoment H extraRaw127step3 := by
      have hz : ∀ j, extraRaw127step2 (extraPermutation6 0) j = 0 := by decide +kernel
      have heq : extraRaw127step3 = (fun u v => extraRaw127step2 (extraPermutation6 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw127step2 extraPermutation6 hz
    injectiveMoment H extraRaw127step3 = injectiveMoment H extraRaw127step4 := by
      have heq : extraRaw127step4 = (fun u v => extraRaw127step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw127step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
