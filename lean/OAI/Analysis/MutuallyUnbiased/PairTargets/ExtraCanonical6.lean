import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraPermutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw96 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def extraRaw96step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def extraRaw96step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem extraCanonical96 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw96 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H extraRaw96 = injectiveMoment H extraRaw96step0 := by
      have hz : ∀ j, extraRaw96 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw96step0 = (fun u v => extraRaw96 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw96 extraPermutation62 hz
    injectiveMoment H extraRaw96step0 = injectiveMoment H extraRaw96step1 := by
      have heq : extraRaw96step1 = (fun u v => extraRaw96step0 (extraPermutation40 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw96step0 extraPermutation40 extraPermutation5
    _ = injectiveMoment H node1294 := by rfl

def extraRaw97 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]]

def extraRaw97step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]]

def extraRaw97step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem extraCanonical97 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw97 = injectiveMoment H node2711 := by
  calc
    injectiveMoment H extraRaw97 = injectiveMoment H extraRaw97step0 := by
      have hz : ∀ j, extraRaw97 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw97step0 = (fun u v => extraRaw97 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw97 extraPermutation62 hz
    injectiveMoment H extraRaw97step0 = injectiveMoment H extraRaw97step1 := by
      have heq : extraRaw97step1 = (fun u v => extraRaw97step0 (extraPermutation55 u) (extraPermutation16 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw97step0 extraPermutation55 extraPermutation16
    _ = injectiveMoment H node2711 := by rfl

def extraRaw98 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw98step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw98step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![1, -1], ![-1, 1]]

def extraRaw98step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical98 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw98 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw98 = injectiveMoment H extraRaw98step0 := by
      have hz : ∀ j, extraRaw98 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw98step0 = (fun u v => extraRaw98 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw98 extraPermutation66 hz
    injectiveMoment H extraRaw98step0 = injectiveMoment H extraRaw98step1 := by
      have hz : ∀ j, extraRaw98step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw98step1 = (fun u v => extraRaw98step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw98step0 extraPermutation39 hz
    injectiveMoment H extraRaw98step1 = injectiveMoment H extraRaw98step2 := by
      have heq : extraRaw98step2 = (fun u v => extraRaw98step1 (extraPermutation13 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw98step1 extraPermutation13 extraPermutation0
    _ = injectiveMoment H node65 := by rfl

def extraRaw99 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw99step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]

def extraRaw99step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]

def extraRaw99step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem extraCanonical99 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw99 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H extraRaw99 = injectiveMoment H extraRaw99step0 := by
      have heq : extraRaw99step0 = -extraRaw99 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw99).symm
    injectiveMoment H extraRaw99step0 = injectiveMoment H extraRaw99step1 := by
      have hz : ∀ j, extraRaw99step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw99step1 = (fun u v => extraRaw99step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw99step0 extraPermutation62 hz
    injectiveMoment H extraRaw99step1 = injectiveMoment H extraRaw99step2 := by
      have heq : extraRaw99step2 = (fun u v => extraRaw99step1 (extraPermutation31 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw99step1 extraPermutation31 extraPermutation3
    _ = injectiveMoment H node1141 := by rfl

def extraRaw100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw100 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw100 = injectiveMoment H extraRaw100step0 := by
      have hz : ∀ j, extraRaw100 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw100step0 = (fun u v => extraRaw100 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw100 extraPermutation62 hz
    injectiveMoment H extraRaw100step0 = injectiveMoment H extraRaw100step1 := by
      have heq : extraRaw100step1 = (fun u v => extraRaw100step0 (extraPermutation34 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw100step0 extraPermutation34 extraPermutation4
    _ = injectiveMoment H node1151 := by rfl

def extraRaw101 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem extraCanonical101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw101 = injectiveMoment H node284 := by
  calc
    injectiveMoment H extraRaw101 = injectiveMoment H extraRaw101step0 := by
      have hz : ∀ j, extraRaw101 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw101step0 = (fun u v => extraRaw101 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw101 extraPermutation63 hz
    injectiveMoment H extraRaw101step0 = injectiveMoment H extraRaw101step1 := by
      have hz : ∀ j, extraRaw101step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw101step1 = (fun u v => extraRaw101step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw101step0 extraPermutation39 hz
    injectiveMoment H extraRaw101step1 = injectiveMoment H extraRaw101step2 := by
      have heq : extraRaw101step2 = (fun u v => extraRaw101step1 (extraPermutation22 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw101step1 extraPermutation22 extraPermutation3
    _ = injectiveMoment H node284 := by rfl

def extraRaw102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def extraRaw102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]

def extraRaw102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]

def extraRaw102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem extraCanonical102 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw102 = injectiveMoment H node711 := by
  calc
    injectiveMoment H extraRaw102 = injectiveMoment H extraRaw102step0 := by
      have heq : extraRaw102step0 = -extraRaw102 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw102).symm
    injectiveMoment H extraRaw102step0 = injectiveMoment H extraRaw102step1 := by
      have hz : ∀ j, extraRaw102step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw102step1 = (fun u v => extraRaw102step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw102step0 extraPermutation62 hz
    injectiveMoment H extraRaw102step1 = injectiveMoment H extraRaw102step2 := by
      have heq : extraRaw102step2 = (fun u v => extraRaw102step1 (extraPermutation29 u) (extraPermutation6 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw102step1 extraPermutation29 extraPermutation6
    _ = injectiveMoment H node711 := by rfl

def extraRaw103 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]]

def extraRaw103step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, 0, 0, 0], ![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 1, 1]]

def extraRaw103step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 1, 1]]

def extraRaw103step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem extraCanonical103 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw103 = injectiveMoment H node2204 := by
  calc
    injectiveMoment H extraRaw103 = injectiveMoment H extraRaw103step0 := by
      have heq : extraRaw103step0 = -extraRaw103 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw103).symm
    injectiveMoment H extraRaw103step0 = injectiveMoment H extraRaw103step1 := by
      have hz : ∀ j, extraRaw103step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw103step1 = (fun u v => extraRaw103step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw103step0 extraPermutation62 hz
    injectiveMoment H extraRaw103step1 = injectiveMoment H extraRaw103step2 := by
      have heq : extraRaw103step2 = (fun u v => extraRaw103step1 (extraPermutation29 u) (extraPermutation16 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw103step1 extraPermutation29 extraPermutation16
    _ = injectiveMoment H node2204 := by rfl

def extraRaw104 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw104step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw104 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw104 = injectiveMoment H extraRaw104step0 := by
      have hz : ∀ j, extraRaw104 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw104step0 = (fun u v => extraRaw104 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw104 extraPermutation63 hz
    injectiveMoment H extraRaw104step0 = injectiveMoment H extraRaw104step1 := by
      have hz : ∀ j, extraRaw104step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw104step1 = (fun u v => extraRaw104step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw104step0 extraPermutation39 hz
    injectiveMoment H extraRaw104step1 = injectiveMoment H extraRaw104step2 := by
      have hz : ∀ j, extraRaw104step1 (extraPermutation12 0) j = 0 := by decide +kernel
      have heq : extraRaw104step2 = (fun u v => extraRaw104step1 (extraPermutation12 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw104step1 extraPermutation12 hz
    injectiveMoment H extraRaw104step2 = injectiveMoment H extraRaw104step3 := by
      have hz : ∀ j, extraRaw104step2 (extraPermutation2 0) j = 0 := by decide +kernel
      have heq : extraRaw104step3 = (fun u v => extraRaw104step2 (extraPermutation2 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw104step2 extraPermutation2 hz
    injectiveMoment H extraRaw104step3 = injectiveMoment H extraRaw104step4 := by
      have heq : extraRaw104step4 = (fun u v => extraRaw104step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw104step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw105 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![-1, 2, -1]]

def extraRaw105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![-1, 2, -1]]

def extraRaw105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1]]

def extraRaw105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem extraCanonical105 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw105 = injectiveMoment H node288 := by
  calc
    injectiveMoment H extraRaw105 = injectiveMoment H extraRaw105step0 := by
      have hz : ∀ j, extraRaw105 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw105step0 = (fun u v => extraRaw105 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw105 extraPermutation63 hz
    injectiveMoment H extraRaw105step0 = injectiveMoment H extraRaw105step1 := by
      have hz : ∀ j, extraRaw105step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw105step1 = (fun u v => extraRaw105step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw105step0 extraPermutation39 hz
    injectiveMoment H extraRaw105step1 = injectiveMoment H extraRaw105step2 := by
      have heq : extraRaw105step2 = (fun u v => extraRaw105step1 (extraPermutation21 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw105step1 extraPermutation21 extraPermutation3
    _ = injectiveMoment H node288 := by rfl

def extraRaw106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem extraCanonical106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw106 = injectiveMoment H node1135 := by
  calc
    injectiveMoment H extraRaw106 = injectiveMoment H extraRaw106step0 := by
      have hz : ∀ j, extraRaw106 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw106step0 = (fun u v => extraRaw106 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw106 extraPermutation62 hz
    injectiveMoment H extraRaw106step0 = injectiveMoment H extraRaw106step1 := by
      have heq : extraRaw106step1 = (fun u v => extraRaw106step0 (extraPermutation28 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw106step0 extraPermutation28 extraPermutation2
    _ = injectiveMoment H node1135 := by rfl

def extraRaw107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]

def extraRaw107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]

def extraRaw107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem extraCanonical107 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw107 = injectiveMoment H node1135 := by
  calc
    injectiveMoment H extraRaw107 = injectiveMoment H extraRaw107step0 := by
      have hz : ∀ j, extraRaw107 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw107step0 = (fun u v => extraRaw107 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw107 extraPermutation62 hz
    injectiveMoment H extraRaw107step0 = injectiveMoment H extraRaw107step1 := by
      have heq : extraRaw107step1 = (fun u v => extraRaw107step0 (extraPermutation54 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw107step0 extraPermutation54 extraPermutation3
    _ = injectiveMoment H node1135 := by rfl

def extraRaw108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]

def extraRaw108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]

def extraRaw108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem extraCanonical108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw108 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H extraRaw108 = injectiveMoment H extraRaw108step0 := by
      have hz : ∀ j, extraRaw108 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw108step0 = (fun u v => extraRaw108 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw108 extraPermutation62 hz
    injectiveMoment H extraRaw108step0 = injectiveMoment H extraRaw108step1 := by
      have heq : extraRaw108step1 = (fun u v => extraRaw108step0 (extraPermutation43 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw108step0 extraPermutation43 extraPermutation5
    _ = injectiveMoment H node1294 := by rfl

def extraRaw109 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 2, -1, -1]]

def extraRaw109step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 2, -1, -1]]

def extraRaw109step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem extraCanonical109 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw109 = injectiveMoment H node2712 := by
  calc
    injectiveMoment H extraRaw109 = injectiveMoment H extraRaw109step0 := by
      have hz : ∀ j, extraRaw109 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw109step0 = (fun u v => extraRaw109 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw109 extraPermutation62 hz
    injectiveMoment H extraRaw109step0 = injectiveMoment H extraRaw109step1 := by
      have heq : extraRaw109step1 = (fun u v => extraRaw109step0 (extraPermutation51 u) (extraPermutation16 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw109step0 extraPermutation51 extraPermutation16
    _ = injectiveMoment H node2712 := by rfl

def extraRaw110 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2]]

def extraRaw110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2]]

def extraRaw110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2]]

def extraRaw110step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem extraCanonical110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw110 = injectiveMoment H node46 := by
  calc
    injectiveMoment H extraRaw110 = injectiveMoment H extraRaw110step0 := by
      have hz : ∀ j, extraRaw110 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw110step0 = (fun u v => extraRaw110 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw110 extraPermutation63 hz
    injectiveMoment H extraRaw110step0 = injectiveMoment H extraRaw110step1 := by
      have hz : ∀ j, extraRaw110step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw110step1 = (fun u v => extraRaw110step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw110step0 extraPermutation39 hz
    injectiveMoment H extraRaw110step1 = injectiveMoment H extraRaw110step2 := by
      have hz : ∀ j, extraRaw110step1 j (extraPermutation2 0) = 0 := by decide +kernel
      have heq : extraRaw110step2 = (fun u v => extraRaw110step1 u (extraPermutation2 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw110step1 extraPermutation2 hz
    _ = injectiveMoment H node46 := by rfl

def extraRaw111 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![-2, 2]]

def extraRaw111step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw111step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw111step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-2, 2]]

def extraRaw111step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem extraCanonical111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw111 = injectiveMoment H node11 := by
  calc
    injectiveMoment H extraRaw111 = injectiveMoment H extraRaw111step0 := by
      have hz : ∀ j, extraRaw111 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw111step0 = (fun u v => extraRaw111 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw111 extraPermutation66 hz
    injectiveMoment H extraRaw111step0 = injectiveMoment H extraRaw111step1 := by
      have hz : ∀ j, extraRaw111step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw111step1 = (fun u v => extraRaw111step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw111step0 extraPermutation39 hz
    injectiveMoment H extraRaw111step1 = injectiveMoment H extraRaw111step2 := by
      have hz : ∀ j, extraRaw111step1 (extraPermutation12 0) j = 0 := by decide +kernel
      have heq : extraRaw111step2 = (fun u v => extraRaw111step1 (extraPermutation12 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw111step1 extraPermutation12 hz
    injectiveMoment H extraRaw111step2 = injectiveMoment H extraRaw111step3 := by
      have heq : extraRaw111step3 = (fun u v => extraRaw111step2 (extraPermutation6 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw111step2 extraPermutation6 extraPermutation0
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
