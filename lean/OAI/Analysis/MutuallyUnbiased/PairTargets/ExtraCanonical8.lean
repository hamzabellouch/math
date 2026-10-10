import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraPermutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw128 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw128step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem extraCanonical128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw128 = injectiveMoment H node383 := by
  calc
    injectiveMoment H extraRaw128 = injectiveMoment H extraRaw128step0 := by
      have heq : extraRaw128step0 = (fun u v => extraRaw128 (extraPermutation57 u) (extraPermutation1 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw128 extraPermutation57 extraPermutation1
    _ = injectiveMoment H node383 := by rfl

def extraRaw129 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem extraCanonical129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw129 = injectiveMoment H node1880 := by
  calc
    injectiveMoment H extraRaw129 = injectiveMoment H extraRaw129step0 := by
      have heq : extraRaw129step0 = (fun u v => extraRaw129 (extraPermutation58 u) (extraPermutation7 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw129 extraPermutation58 extraPermutation7
    _ = injectiveMoment H node1880 := by rfl

def extraRaw130 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw130step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw130step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def extraRaw130step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0]]

def extraRaw130step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem extraCanonical130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw130 = injectiveMoment H node4 := by
  calc
    injectiveMoment H extraRaw130 = injectiveMoment H extraRaw130step0 := by
      have hz : ∀ j, extraRaw130 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw130step0 = (fun u v => extraRaw130 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw130 extraPermutation67 hz
    injectiveMoment H extraRaw130step0 = injectiveMoment H extraRaw130step1 := by
      have hz : ∀ j, extraRaw130step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw130step1 = (fun u v => extraRaw130step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw130step0 extraPermutation49 hz
    injectiveMoment H extraRaw130step1 = injectiveMoment H extraRaw130step2 := by
      have hz : ∀ j, extraRaw130step1 (extraPermutation20 0) j = 0 := by decide +kernel
      have heq : extraRaw130step2 = (fun u v => extraRaw130step1 (extraPermutation20 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw130step1 extraPermutation20 hz
    injectiveMoment H extraRaw130step2 = injectiveMoment H extraRaw130step3 := by
      have hz : ∀ j, extraRaw130step2 (extraPermutation6 0) j = 0 := by decide +kernel
      have heq : extraRaw130step3 = (fun u v => extraRaw130step2 (extraPermutation6 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw130step2 extraPermutation6 hz
    _ = injectiveMoment H node4 := by rfl

def extraRaw131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]

def extraRaw131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]

def extraRaw131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0]]

def extraRaw131step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0]]

def extraRaw131step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2]]

def extraRaw131step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw131step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem extraCanonical131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw131 = injectiveMoment H node4 := by
  calc
    injectiveMoment H extraRaw131 = injectiveMoment H extraRaw131step0 := by
      have hz : ∀ j, extraRaw131 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw131step0 = (fun u v => extraRaw131 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw131 extraPermutation67 hz
    injectiveMoment H extraRaw131step0 = injectiveMoment H extraRaw131step1 := by
      have hz : ∀ j, extraRaw131step0 (extraPermutation49 0) j = 0 := by decide +kernel
      have heq : extraRaw131step1 = (fun u v => extraRaw131step0 (extraPermutation49 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw131step0 extraPermutation49 hz
    injectiveMoment H extraRaw131step1 = injectiveMoment H extraRaw131step2 := by
      have hz : ∀ j, extraRaw131step1 (extraPermutation20 0) j = 0 := by decide +kernel
      have heq : extraRaw131step2 = (fun u v => extraRaw131step1 (extraPermutation20 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw131step1 extraPermutation20 hz
    injectiveMoment H extraRaw131step2 = injectiveMoment H extraRaw131step3 := by
      have hz : ∀ j, extraRaw131step2 (extraPermutation6 0) j = 0 := by decide +kernel
      have heq : extraRaw131step3 = (fun u v => extraRaw131step2 (extraPermutation6 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw131step2 extraPermutation6 hz
    injectiveMoment H extraRaw131step3 = injectiveMoment H extraRaw131step4 := by
      have hz : ∀ j, extraRaw131step3 j (extraPermutation2 0) = 0 := by decide +kernel
      have heq : extraRaw131step4 = (fun u v => extraRaw131step3 u (extraPermutation2 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw131step3 extraPermutation2 hz
    injectiveMoment H extraRaw131step4 = injectiveMoment H extraRaw131step5 := by
      have heq : extraRaw131step5 = (fun u v => extraRaw131step4 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw131step4 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node4 := by rfl

def extraRaw132 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw132step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem extraCanonical132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw132 = injectiveMoment H node383 := by
  calc
    injectiveMoment H extraRaw132 = injectiveMoment H extraRaw132step0 := by
      have heq : extraRaw132step0 = (fun u v => extraRaw132 (extraPermutation60 u) (extraPermutation1 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw132 extraPermutation60 extraPermutation1
    _ = injectiveMoment H node383 := by rfl

def extraRaw133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def extraRaw133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem extraCanonical133 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw133 = injectiveMoment H node1880 := by
  calc
    injectiveMoment H extraRaw133 = injectiveMoment H extraRaw133step0 := by
      have heq : extraRaw133step0 = -extraRaw133 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw133).symm
    injectiveMoment H extraRaw133step0 = injectiveMoment H extraRaw133step1 := by
      have heq : extraRaw133step1 = (fun u v => extraRaw133step0 (extraPermutation61 u) (extraPermutation6 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw133step0 extraPermutation61 extraPermutation6
    _ = injectiveMoment H node1880 := by rfl

def extraRaw134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![3, -2, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem extraCanonical134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw134 = injectiveMoment H node1880 := by
  calc
    injectiveMoment H extraRaw134 = injectiveMoment H extraRaw134step0 := by
      have heq : extraRaw134step0 = (fun u v => extraRaw134 (extraPermutation61 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw134 extraPermutation61 extraPermutation5
    _ = injectiveMoment H node1880 := by rfl

def extraRaw135 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem extraCanonical135 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw135 = injectiveMoment H node1880 := by
  calc
    injectiveMoment H extraRaw135 = injectiveMoment H extraRaw135step0 := by
      have heq : extraRaw135step0 = -extraRaw135 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw135).symm
    injectiveMoment H extraRaw135step0 = injectiveMoment H extraRaw135step1 := by
      have heq : extraRaw135step1 = (fun u v => extraRaw135step0 (extraPermutation58 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw135step0 extraPermutation58 extraPermutation4
    _ = injectiveMoment H node1880 := by rfl

def extraRaw136 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, -2, -1, 2], ![1, 0, -1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def extraRaw136step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

theorem extraCanonical136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw136 = injectiveMoment H node3320 := by
  calc
    injectiveMoment H extraRaw136 = injectiveMoment H extraRaw136step0 := by
      have heq : extraRaw136step0 = (fun u v => extraRaw136 (extraPermutation61 u) (extraPermutation14 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw136 extraPermutation61 extraPermutation14
    _ = injectiveMoment H node3320 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
