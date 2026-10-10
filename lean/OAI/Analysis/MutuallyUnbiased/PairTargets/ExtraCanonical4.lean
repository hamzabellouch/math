import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraPermutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw64 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, 1, -2]]

def extraRaw64step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![0, 2, -2], ![1, 1, -2]]

def extraRaw64step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem extraCanonical64 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw64 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw64 = injectiveMoment H extraRaw64step0 := by
      have hz : ∀ j, extraRaw64 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw64step0 = (fun u v => extraRaw64 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw64 extraPermutation62 hz
    injectiveMoment H extraRaw64step0 = injectiveMoment H extraRaw64step1 := by
      have heq : extraRaw64step1 = (fun u v => extraRaw64step0 (extraPermutation26 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw64step0 extraPermutation26 extraPermutation2
    _ = injectiveMoment H node858 := by rfl

def extraRaw65 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![0, 0]]

def extraRaw65step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw65step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw65step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw65step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw65step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem extraCanonical65 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw65 = injectiveMoment H node5 := by
  calc
    injectiveMoment H extraRaw65 = injectiveMoment H extraRaw65step0 := by
      have hz : ∀ j, extraRaw65 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw65step0 = (fun u v => extraRaw65 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw65 extraPermutation67 hz
    injectiveMoment H extraRaw65step0 = injectiveMoment H extraRaw65step1 := by
      have hz : ∀ j, extraRaw65step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw65step1 = (fun u v => extraRaw65step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw65step0 extraPermutation39 hz
    injectiveMoment H extraRaw65step1 = injectiveMoment H extraRaw65step2 := by
      have hz : ∀ j, extraRaw65step1 (extraPermutation12 0) j = 0 := by decide +kernel
      have heq : extraRaw65step2 = (fun u v => extraRaw65step1 (extraPermutation12 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw65step1 extraPermutation12 hz
    injectiveMoment H extraRaw65step2 = injectiveMoment H extraRaw65step3 := by
      have hz : ∀ j, extraRaw65step2 (extraPermutation2 0) j = 0 := by decide +kernel
      have heq : extraRaw65step3 = (fun u v => extraRaw65step2 (extraPermutation2 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw65step2 extraPermutation2 hz
    injectiveMoment H extraRaw65step3 = injectiveMoment H extraRaw65step4 := by
      have heq : extraRaw65step4 = (fun u v => extraRaw65step3 (extraPermutation1 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw65step3 extraPermutation1 extraPermutation0
    _ = injectiveMoment H node5 := by rfl

def extraRaw66 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw66step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw66step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem extraCanonical66 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw66 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H extraRaw66 = injectiveMoment H extraRaw66step0 := by
      have hz : ∀ j, extraRaw66 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw66step0 = (fun u v => extraRaw66 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw66 extraPermutation62 hz
    injectiveMoment H extraRaw66step0 = injectiveMoment H extraRaw66step1 := by
      have heq : extraRaw66step1 = (fun u v => extraRaw66step0 (extraPermutation46 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw66step0 extraPermutation46 extraPermutation3
    _ = injectiveMoment H node1152 := by rfl

def extraRaw67 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw67step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw67step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical67 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw67 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw67 = injectiveMoment H extraRaw67step0 := by
      have hz : ∀ j, extraRaw67 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw67step0 = (fun u v => extraRaw67 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw67 extraPermutation62 hz
    injectiveMoment H extraRaw67step0 = injectiveMoment H extraRaw67step1 := by
      have heq : extraRaw67step1 = (fun u v => extraRaw67step0 (extraPermutation25 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw67step0 extraPermutation25 extraPermutation4
    _ = injectiveMoment H node1151 := by rfl

def extraRaw68 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw68step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw68step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw68step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem extraCanonical68 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw68 = injectiveMoment H node283 := by
  calc
    injectiveMoment H extraRaw68 = injectiveMoment H extraRaw68step0 := by
      have hz : ∀ j, extraRaw68 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw68step0 = (fun u v => extraRaw68 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw68 extraPermutation63 hz
    injectiveMoment H extraRaw68step0 = injectiveMoment H extraRaw68step1 := by
      have hz : ∀ j, extraRaw68step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw68step1 = (fun u v => extraRaw68step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw68step0 extraPermutation39 hz
    injectiveMoment H extraRaw68step1 = injectiveMoment H extraRaw68step2 := by
      have heq : extraRaw68step2 = (fun u v => extraRaw68step1 (extraPermutation19 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw68step1 extraPermutation19 extraPermutation3
    _ = injectiveMoment H node283 := by rfl

def extraRaw69 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]

def extraRaw69step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]

def extraRaw69step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem extraCanonical69 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw69 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H extraRaw69 = injectiveMoment H extraRaw69step0 := by
      have hz : ∀ j, extraRaw69 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw69step0 = (fun u v => extraRaw69 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw69 extraPermutation62 hz
    injectiveMoment H extraRaw69step0 = injectiveMoment H extraRaw69step1 := by
      have heq : extraRaw69step1 = (fun u v => extraRaw69step0 (extraPermutation41 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw69step0 extraPermutation41 extraPermutation5
    _ = injectiveMoment H node1294 := by rfl

def extraRaw70 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]]

def extraRaw70step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]]

def extraRaw70step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem extraCanonical70 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw70 = injectiveMoment H node2711 := by
  calc
    injectiveMoment H extraRaw70 = injectiveMoment H extraRaw70step0 := by
      have hz : ∀ j, extraRaw70 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw70step0 = (fun u v => extraRaw70 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw70 extraPermutation62 hz
    injectiveMoment H extraRaw70step0 = injectiveMoment H extraRaw70step1 := by
      have heq : extraRaw70step1 = (fun u v => extraRaw70step0 (extraPermutation48 u) (extraPermutation16 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw70step0 extraPermutation48 extraPermutation16
    _ = injectiveMoment H node2711 := by rfl

def extraRaw71 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![-1, 1], ![0, 0]]

def extraRaw71step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw71step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![1, -1], ![-1, 1]]

def extraRaw71step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem extraCanonical71 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw71 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw71 = injectiveMoment H extraRaw71step0 := by
      have hz : ∀ j, extraRaw71 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw71step0 = (fun u v => extraRaw71 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw71 extraPermutation67 hz
    injectiveMoment H extraRaw71step0 = injectiveMoment H extraRaw71step1 := by
      have hz : ∀ j, extraRaw71step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw71step1 = (fun u v => extraRaw71step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw71step0 extraPermutation39 hz
    injectiveMoment H extraRaw71step1 = injectiveMoment H extraRaw71step2 := by
      have heq : extraRaw71step2 = (fun u v => extraRaw71step1 (extraPermutation13 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw71step1 extraPermutation13 extraPermutation0
    _ = injectiveMoment H node65 := by rfl

def extraRaw72 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw72step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]

def extraRaw72step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]

def extraRaw72step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem extraCanonical72 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw72 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H extraRaw72 = injectiveMoment H extraRaw72step0 := by
      have heq : extraRaw72step0 = -extraRaw72 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw72).symm
    injectiveMoment H extraRaw72step0 = injectiveMoment H extraRaw72step1 := by
      have hz : ∀ j, extraRaw72step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw72step1 = (fun u v => extraRaw72step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw72step0 extraPermutation62 hz
    injectiveMoment H extraRaw72step1 = injectiveMoment H extraRaw72step2 := by
      have heq : extraRaw72step2 = (fun u v => extraRaw72step1 (extraPermutation33 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw72step1 extraPermutation33 extraPermutation3
    _ = injectiveMoment H node1141 := by rfl

def extraRaw73 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw73step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw73step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem extraCanonical73 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw73 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H extraRaw73 = injectiveMoment H extraRaw73step0 := by
      have hz : ∀ j, extraRaw73 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw73step0 = (fun u v => extraRaw73 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw73 extraPermutation62 hz
    injectiveMoment H extraRaw73step0 = injectiveMoment H extraRaw73step1 := by
      have heq : extraRaw73step1 = (fun u v => extraRaw73step0 (extraPermutation35 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw73step0 extraPermutation35 extraPermutation4
    _ = injectiveMoment H node1151 := by rfl

def extraRaw74 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw74step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw74step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw74step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem extraCanonical74 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw74 = injectiveMoment H node284 := by
  calc
    injectiveMoment H extraRaw74 = injectiveMoment H extraRaw74step0 := by
      have hz : ∀ j, extraRaw74 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw74step0 = (fun u v => extraRaw74 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw74 extraPermutation63 hz
    injectiveMoment H extraRaw74step0 = injectiveMoment H extraRaw74step1 := by
      have hz : ∀ j, extraRaw74step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw74step1 = (fun u v => extraRaw74step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw74step0 extraPermutation39 hz
    injectiveMoment H extraRaw74step1 = injectiveMoment H extraRaw74step2 := by
      have heq : extraRaw74step2 = (fun u v => extraRaw74step1 (extraPermutation18 u) (extraPermutation3 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw74step1 extraPermutation18 extraPermutation3
    _ = injectiveMoment H node284 := by rfl

def extraRaw75 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]

def extraRaw75step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]

def extraRaw75step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]

def extraRaw75step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem extraCanonical75 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw75 = injectiveMoment H node711 := by
  calc
    injectiveMoment H extraRaw75 = injectiveMoment H extraRaw75step0 := by
      have heq : extraRaw75step0 = -extraRaw75 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw75).symm
    injectiveMoment H extraRaw75step0 = injectiveMoment H extraRaw75step1 := by
      have hz : ∀ j, extraRaw75step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw75step1 = (fun u v => extraRaw75step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw75step0 extraPermutation62 hz
    injectiveMoment H extraRaw75step1 = injectiveMoment H extraRaw75step2 := by
      have heq : extraRaw75step2 = (fun u v => extraRaw75step1 (extraPermutation30 u) (extraPermutation6 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw75step1 extraPermutation30 extraPermutation6
    _ = injectiveMoment H node711 := by rfl

def extraRaw76 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]]

def extraRaw76step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, 0, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![-1, -1, 1, 1]]

def extraRaw76step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![-1, -1, 1, 1]]

def extraRaw76step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem extraCanonical76 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw76 = injectiveMoment H node2204 := by
  calc
    injectiveMoment H extraRaw76 = injectiveMoment H extraRaw76step0 := by
      have heq : extraRaw76step0 = -extraRaw76 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw76).symm
    injectiveMoment H extraRaw76step0 = injectiveMoment H extraRaw76step1 := by
      have hz : ∀ j, extraRaw76step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw76step1 = (fun u v => extraRaw76step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw76step0 extraPermutation62 hz
    injectiveMoment H extraRaw76step1 = injectiveMoment H extraRaw76step2 := by
      have heq : extraRaw76step2 = (fun u v => extraRaw76step1 (extraPermutation30 u) (extraPermutation16 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw76step1 extraPermutation30 extraPermutation16
    _ = injectiveMoment H node2204 := by rfl

def extraRaw77 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1]]

def extraRaw77step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1]]

def extraRaw77step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1]]

def extraRaw77step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def extraRaw77step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem extraCanonical77 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw77 = injectiveMoment H node46 := by
  calc
    injectiveMoment H extraRaw77 = injectiveMoment H extraRaw77step0 := by
      have hz : ∀ j, extraRaw77 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw77step0 = (fun u v => extraRaw77 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw77 extraPermutation63 hz
    injectiveMoment H extraRaw77step0 = injectiveMoment H extraRaw77step1 := by
      have hz : ∀ j, extraRaw77step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw77step1 = (fun u v => extraRaw77step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw77step0 extraPermutation39 hz
    injectiveMoment H extraRaw77step1 = injectiveMoment H extraRaw77step2 := by
      have hz : ∀ j, extraRaw77step1 j (extraPermutation2 0) = 0 := by decide +kernel
      have heq : extraRaw77step2 = (fun u v => extraRaw77step1 u (extraPermutation2 v.succ)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H extraRaw77step1 extraPermutation2 hz
    injectiveMoment H extraRaw77step2 = injectiveMoment H extraRaw77step3 := by
      have heq : extraRaw77step3 = (fun u v => extraRaw77step2 (extraPermutation9 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw77step2 extraPermutation9 extraPermutation0
    _ = injectiveMoment H node46 := by rfl

def extraRaw78 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-2, 2], ![0, 0]]

def extraRaw78step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw78step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw78step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-2, 2]]

def extraRaw78step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem extraCanonical78 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw78 = injectiveMoment H node11 := by
  calc
    injectiveMoment H extraRaw78 = injectiveMoment H extraRaw78step0 := by
      have hz : ∀ j, extraRaw78 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw78step0 = (fun u v => extraRaw78 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw78 extraPermutation67 hz
    injectiveMoment H extraRaw78step0 = injectiveMoment H extraRaw78step1 := by
      have hz : ∀ j, extraRaw78step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw78step1 = (fun u v => extraRaw78step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw78step0 extraPermutation39 hz
    injectiveMoment H extraRaw78step1 = injectiveMoment H extraRaw78step2 := by
      have hz : ∀ j, extraRaw78step1 (extraPermutation12 0) j = 0 := by decide +kernel
      have heq : extraRaw78step2 = (fun u v => extraRaw78step1 (extraPermutation12 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw78step1 extraPermutation12 hz
    injectiveMoment H extraRaw78step2 = injectiveMoment H extraRaw78step3 := by
      have heq : extraRaw78step3 = (fun u v => extraRaw78step2 (extraPermutation6 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw78step2 extraPermutation6 extraPermutation0
    _ = injectiveMoment H node11 := by rfl

def extraRaw79 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1]]

def extraRaw79step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, 0, 1]]

def extraRaw79step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, 0, 1]]

def extraRaw79step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem extraCanonical79 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw79 = injectiveMoment H node659 := by
  calc
    injectiveMoment H extraRaw79 = injectiveMoment H extraRaw79step0 := by
      have heq : extraRaw79step0 = -extraRaw79 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw79).symm
    injectiveMoment H extraRaw79step0 = injectiveMoment H extraRaw79step1 := by
      have hz : ∀ j, extraRaw79step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw79step1 = (fun u v => extraRaw79step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw79step0 extraPermutation62 hz
    injectiveMoment H extraRaw79step1 = injectiveMoment H extraRaw79step2 := by
      have heq : extraRaw79step2 = (fun u v => extraRaw79step1 (extraPermutation47 u) (extraPermutation4 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw79step1 extraPermutation47 extraPermutation4
    _ = injectiveMoment H node659 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
