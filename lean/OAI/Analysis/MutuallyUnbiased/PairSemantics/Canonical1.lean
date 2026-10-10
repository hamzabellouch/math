import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw32 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]

def raw32step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 0, 2], ![-3, 2, 1]]

def raw32step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

theorem canonical32 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw32 = injectiveMoment H node27 := by
  calc
    injectiveMoment H raw32 = injectiveMoment H raw32step0 := by
      have heq : raw32step0 = -raw32 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw32).symm
    injectiveMoment H raw32step0 = injectiveMoment H raw32step1 := by
      have heq : raw32step1 = (fun i j => raw32step0 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw32step0 permutation3 permutation6
    _ = injectiveMoment H node27 := by rfl

def raw33 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]

def raw33step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, -1, 3], ![-3, 3, 0]]

def raw33step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]

theorem canonical33 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw33 = injectiveMoment H node17 := by
  calc
    injectiveMoment H raw33 = injectiveMoment H raw33step0 := by
      have heq : raw33step0 = -raw33 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw33).symm
    injectiveMoment H raw33step0 = injectiveMoment H raw33step1 := by
      have heq : raw33step1 = (fun i j => raw33step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw33step0 permutation4 permutation8
    _ = injectiveMoment H node17 := by rfl

def raw34 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]

def raw34step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

theorem canonical34 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw34 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw34 = injectiveMoment H raw34step0 := by
      have heq : raw34step0 = raw34.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw34).symm
    _ = injectiveMoment H node7 := by rfl

def raw35 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 3, 2], ![5, -3, -2]]

def raw35step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![3, -3], ![2, -2]]

def raw35step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

theorem canonical35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw35 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw35 = injectiveMoment H raw35step0 := by
      have heq : raw35step0 = raw35.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw35).symm
    injectiveMoment H raw35step0 = injectiveMoment H raw35step1 := by
      have heq : raw35step1 = (fun i j => raw35step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw35step0 permutation4 permutation1
    _ = injectiveMoment H node7 := by rfl

def raw36 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw36step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw36 = injectiveMoment H node66 := by
  calc
    injectiveMoment H raw36 = injectiveMoment H raw36step0 := by
      have hz : ∀ j, raw36 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw36step0 = (fun i j => raw36 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw36 permutation202 hz
    _ = injectiveMoment H node66 := by rfl

def raw37 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![1, -1], ![3, -3]]

def raw37step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]

theorem canonical37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw37 = injectiveMoment H node12 := by
  calc
    injectiveMoment H raw37 = injectiveMoment H raw37step0 := by
      have hz : ∀ j, raw37 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw37step0 = (fun i j => raw37 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw37 permutation57 hz
    _ = injectiveMoment H node12 := by rfl

def raw38 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![2, -2], ![2, -2]]

def raw38step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical38 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw38 = injectiveMoment H node13 := by
  calc
    injectiveMoment H raw38 = injectiveMoment H raw38step0 := by
      have hz : ∀ j, raw38 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw38step0 = (fun i j => raw38 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw38 permutation57 hz
    _ = injectiveMoment H node13 := by rfl

def raw39 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![4, -4]]

def raw39step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

theorem canonical39 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw39 = injectiveMoment H node6 := by
  calc
    injectiveMoment H raw39 = injectiveMoment H raw39step0 := by
      have hz : ∀ j, raw39 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw39step0 = (fun i j => raw39 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw39 permutation15 hz
    _ = injectiveMoment H node6 := by rfl

def raw40 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![2, -2], ![3, -3]]

def raw40step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

theorem canonical40 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw40 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw40 = injectiveMoment H raw40step0 := by
      have hz : ∀ j, raw40 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw40step0 = (fun i j => raw40 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw40 permutation15 hz
    _ = injectiveMoment H node7 := by rfl

def raw41 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![5, -5]]

def raw41step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]

theorem canonical41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw41 = injectiveMoment H node1 := by
  calc
    injectiveMoment H raw41 = injectiveMoment H raw41step0 := by
      have hz : ∀ j, raw41 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw41step0 = (fun i j => raw41 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw41 permutation5 hz
    _ = injectiveMoment H node1 := by rfl

def raw42 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical42 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw42 = injectiveMoment H node295 := by
  rfl

def raw43 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw43 = injectiveMoment H node66 := by
  rfl

def raw44 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]

def raw44step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw44 = injectiveMoment H node66 := by
  calc
    injectiveMoment H raw44 = injectiveMoment H raw44step0 := by
      have heq : raw44step0 = (fun i j => raw44 (permutation34 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw44 permutation34 permutation1
    _ = injectiveMoment H node66 := by rfl

def raw45 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]

theorem canonical45 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw45 = injectiveMoment H node12 := by
  rfl

def raw46 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]

def raw46step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical46 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw46 = injectiveMoment H node66 := by
  calc
    injectiveMoment H raw46 = injectiveMoment H raw46step0 := by
      have heq : raw46step0 = (fun i j => raw46 (permutation36 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw46 permutation36 permutation1
    _ = injectiveMoment H node66 := by rfl

def raw47 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical47 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw47 = injectiveMoment H node13 := by
  rfl

def raw48 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

theorem canonical48 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw48 = injectiveMoment H node6 := by
  rfl

def raw49 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]

def raw49step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical49 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw49 = injectiveMoment H node66 := by
  calc
    injectiveMoment H raw49 = injectiveMoment H raw49step0 := by
      have heq : raw49step0 = (fun i j => raw49 (permutation42 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw49 permutation42 permutation1
    _ = injectiveMoment H node66 := by rfl

def raw50 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![2, -2]]

def raw50step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical50 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw50 = injectiveMoment H node13 := by
  calc
    injectiveMoment H raw50 = injectiveMoment H raw50step0 := by
      have heq : raw50step0 = (fun i j => raw50 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw50 permutation11 permutation1
    _ = injectiveMoment H node13 := by rfl

def raw51 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

theorem canonical51 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw51 = injectiveMoment H node7 := by
  rfl

def raw52 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![3, -3], ![2, -2]]

def raw52step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

theorem canonical52 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw52 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw52 = injectiveMoment H raw52step0 := by
      have heq : raw52step0 = (fun i j => raw52 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw52 permutation4 permutation1
    _ = injectiveMoment H node7 := by rfl

def raw53 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]

theorem canonical53 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw53 = injectiveMoment H node1 := by
  rfl

def raw54 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 1, 3], ![1, 2, -2, -1], ![3, -2, 1, -2]]

def raw54step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]

def raw54step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]

def raw54step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical54 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw54 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw54 = injectiveMoment H raw54step0 := by
      have heq : raw54step0 = raw54.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw54).symm
    injectiveMoment H raw54step0 = injectiveMoment H raw54step1 := by
      have heq : raw54step1 = -raw54step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw54step0).symm
    injectiveMoment H raw54step1 = injectiveMoment H raw54step2 := by
      have heq : raw54step2 = (fun i j => raw54step1 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw54step1 permutation16 permutation5
    _ = injectiveMoment H node191 := by rfl

def raw55 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 1, 3], ![2, -2, 1, -1], ![2, 2, -2, -2]]

def raw55step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]

def raw55step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, -1, 2], ![-3, 1, 2]]

def raw55step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical55 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw55 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw55 = injectiveMoment H raw55step0 := by
      have heq : raw55step0 = raw55.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw55).symm
    injectiveMoment H raw55step0 = injectiveMoment H raw55step1 := by
      have heq : raw55step1 = -raw55step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw55step0).symm
    injectiveMoment H raw55step1 = injectiveMoment H raw55step2 := by
      have heq : raw55step2 = (fun i j => raw55step1 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw55step1 permutation12 permutation6
    _ = injectiveMoment H node135 := by rfl

def raw56 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 2, 2], ![1, 2, -2, -1], ![3, -2, 0, -1]]

def raw56step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw56step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw56step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw56 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw56 = injectiveMoment H raw56step0 := by
      have heq : raw56step0 = raw56.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw56).symm
    injectiveMoment H raw56step0 = injectiveMoment H raw56step1 := by
      have heq : raw56step1 = -raw56step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw56step0).symm
    injectiveMoment H raw56step1 = injectiveMoment H raw56step2 := by
      have heq : raw56step2 = (fun i j => raw56step1 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw56step1 permutation12 permutation8
    _ = injectiveMoment H node85 := by rfl

def raw57 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 3, 1], ![1, 2, -1, -2], ![3, -2, -2, 1]]

def raw57step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![3, -1, -2], ![1, -2, 1]]

def raw57step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-3, 1, 2], ![-1, 2, -1]]

def raw57step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw57 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw57 = injectiveMoment H raw57step0 := by
      have heq : raw57step0 = raw57.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw57).symm
    injectiveMoment H raw57step0 = injectiveMoment H raw57step1 := by
      have heq : raw57step1 = -raw57step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw57step0).symm
    injectiveMoment H raw57step1 = injectiveMoment H raw57step2 := by
      have heq : raw57step2 = (fun i j => raw57step1 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw57step1 permutation15 permutation5
    _ = injectiveMoment H node191 := by rfl

def raw58 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 3, 1], ![2, -2, -1, 1], ![2, 2, -2, -2]]

def raw58step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![3, -1, -2], ![1, 1, -2]]

def raw58step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-3, 1, 2], ![-1, -1, 2]]

def raw58step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical58 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw58 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw58 = injectiveMoment H raw58step0 := by
      have heq : raw58step0 = raw58.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw58).symm
    injectiveMoment H raw58step0 = injectiveMoment H raw58step1 := by
      have heq : raw58step1 = -raw58step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw58step0).symm
    injectiveMoment H raw58step1 = injectiveMoment H raw58step2 := by
      have heq : raw58step2 = (fun i j => raw58step1 (permutation14 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw58step1 permutation14 permutation6
    _ = injectiveMoment H node135 := by rfl

def raw59 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw59step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical59 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw59 = injectiveMoment H node2789 := by
  calc
    injectiveMoment H raw59 = injectiveMoment H raw59step0 := by
      have heq : raw59step0 = (fun i j => raw59 (permutation252 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw59 permutation252 permutation6
    _ = injectiveMoment H node2789 := by rfl

def raw60 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw60step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical60 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw60 = injectiveMoment H node2658 := by
  calc
    injectiveMoment H raw60 = injectiveMoment H raw60step0 := by
      have heq : raw60step0 = (fun i j => raw60 (permutation389 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw60 permutation389 permutation6
    _ = injectiveMoment H node2658 := by rfl

def raw61 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw61step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical61 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw61 = injectiveMoment H node865 := by
  calc
    injectiveMoment H raw61 = injectiveMoment H raw61step0 := by
      have heq : raw61step0 = (fun i j => raw61 (permutation145 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw61 permutation145 permutation6
    _ = injectiveMoment H node865 := by rfl

def raw62 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw62step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical62 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw62 = injectiveMoment H node565 := by
  calc
    injectiveMoment H raw62 = injectiveMoment H raw62step0 := by
      have heq : raw62step0 = (fun i j => raw62 (permutation145 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw62 permutation145 permutation6
    _ = injectiveMoment H node565 := by rfl

def raw63 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw63step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical63 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw63 = injectiveMoment H node650 := by
  calc
    injectiveMoment H raw63 = injectiveMoment H raw63step0 := by
      have heq : raw63step0 = (fun i j => raw63 (permutation122 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw63 permutation122 permutation6
    _ = injectiveMoment H node650 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
