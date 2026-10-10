import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7968 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, -1, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw7968step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 0, 1], ![0, 1, 3, -4], ![0, 1, -2, 1], ![-1, 0, -1, 2]]

def raw7968step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical7968 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7968 = injectiveMoment H node1278 := by
  calc
    injectiveMoment H raw7968 = injectiveMoment H raw7968step0 := by
      have heq : raw7968step0 = -raw7968 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7968).symm
    injectiveMoment H raw7968step0 = injectiveMoment H raw7968step1 := by
      have heq : raw7968step1 = (fun i j => raw7968step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7968step0 permutation32 permutation9
    _ = injectiveMoment H node1278 := by rfl

def raw7969 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7969step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 0, 1], ![0, 1, 3, -4], ![0, 0, -2, 2], ![-1, 1, -1, 1]]

def raw7969step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical7969 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7969 = injectiveMoment H node1348 := by
  calc
    injectiveMoment H raw7969 = injectiveMoment H raw7969step0 := by
      have heq : raw7969step0 = -raw7969 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7969).symm
    injectiveMoment H raw7969step0 = injectiveMoment H raw7969step1 := by
      have heq : raw7969step1 = (fun i j => raw7969step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7969step0 permutation32 permutation9
    _ = injectiveMoment H node1348 := by rfl

def raw7970 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -2, 3]]

def raw7970step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, -1, -1, 3]]

def raw7970step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical7970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7970 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw7970 = injectiveMoment H raw7970step0 := by
      have heq : raw7970step0 = raw7970.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7970).symm
    injectiveMoment H raw7970step0 = injectiveMoment H raw7970step1 := by
      have heq : raw7970step1 = (fun i j => raw7970step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7970step0 permutation27 permutation17
    _ = injectiveMoment H node959 := by rfl

def raw7971 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, -3, 4]]

def raw7971step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, 1, 2, -3], ![-1, -1, -2, 4]]

def raw7971step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

theorem canonical7971 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7971 = injectiveMoment H node760 := by
  calc
    injectiveMoment H raw7971 = injectiveMoment H raw7971step0 := by
      have heq : raw7971step0 = raw7971.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7971).symm
    injectiveMoment H raw7971step0 = injectiveMoment H raw7971step1 := by
      have heq : raw7971step1 = (fun i j => raw7971step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7971step0 permutation27 permutation17
    _ = injectiveMoment H node760 := by rfl

def raw7972 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, -2, -3, 4]]

def raw7972step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, 2, 1, -3], ![-1, -2, -1, 4]]

def raw7972step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

theorem canonical7972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7972 = injectiveMoment H node760 := by
  calc
    injectiveMoment H raw7972 = injectiveMoment H raw7972step0 := by
      have heq : raw7972step0 = raw7972.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7972).symm
    injectiveMoment H raw7972step0 = injectiveMoment H raw7972step1 := by
      have heq : raw7972step1 = (fun i j => raw7972step0 (permutation27 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7972step0 permutation27 permutation23
    _ = injectiveMoment H node760 := by rfl

def raw7973 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 2, -2], ![1, -2, -2, 3]]

def raw7973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![0, 2, -2], ![-1, -2, 3]]

def raw7973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical7973 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7973 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw7973 = injectiveMoment H raw7973step0 := by
      have heq : raw7973step0 = raw7973.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7973).symm
    injectiveMoment H raw7973step0 = injectiveMoment H raw7973step1 := by
      have heq : raw7973step1 = (fun i j => raw7973step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7973step0 permutation27 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw7974 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -3, 4]]

def raw7974step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![1, 1, 1, -3], ![-2, -1, -1, 4]]

def raw7974step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 1, -3]]

theorem canonical7974 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7974 = injectiveMoment H node904 := by
  calc
    injectiveMoment H raw7974 = injectiveMoment H raw7974step0 := by
      have heq : raw7974step0 = raw7974.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7974).symm
    injectiveMoment H raw7974step0 = injectiveMoment H raw7974step1 := by
      have heq : raw7974step1 = (fun i j => raw7974step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7974step0 permutation27 permutation17
    _ = injectiveMoment H node904 := by rfl

def raw7975 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, 1, -1], ![1, -2, -2, 3]]

def raw7975step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![1, 1, -2], ![-2, -1, 3]]

def raw7975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical7975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7975 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw7975 = injectiveMoment H raw7975step0 := by
      have heq : raw7975step0 = raw7975.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7975).symm
    injectiveMoment H raw7975step0 = injectiveMoment H raw7975step1 := by
      have heq : raw7975step1 = (fun i j => raw7975step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7975step0 permutation27 permutation5
    _ = injectiveMoment H node268 := by rfl

def raw7976 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, 2, -2], ![1, -2, -3, 4]]

def raw7976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![1, 2, -3], ![-2, -2, 4]]

def raw7976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

theorem canonical7976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7976 = injectiveMoment H node140 := by
  calc
    injectiveMoment H raw7976 = injectiveMoment H raw7976step0 := by
      have heq : raw7976step0 = raw7976.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7976).symm
    injectiveMoment H raw7976step0 = injectiveMoment H raw7976step1 := by
      have heq : raw7976step1 = (fun i j => raw7976step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7976step0 permutation27 permutation5
    _ = injectiveMoment H node140 := by rfl

def raw7977 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -3, 2]]

def raw7977step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![3, -3], ![-2, 2]]

def raw7977step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw7978 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7978step0 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7978step1 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7978step2 : Matrix (Fin 0) (Fin 0) ℤ := ![]

theorem canonical7978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7978 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7978 = injectiveMoment H raw7978step0 := by
      have hz : ∀ j, raw7978 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7978step0 = (fun i j => raw7978 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7978 permutation2 hz
    injectiveMoment H raw7978step0 = injectiveMoment H raw7978step1 := by
      have hz : ∀ j, raw7978step0 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7978step1 = (fun i j => raw7978step0 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7978step0 permutation0 hz
    injectiveMoment H raw7978step1 = injectiveMoment H raw7978step2 := by
      have hz : ∀ i, raw7978step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7978step2 = (fun i j => raw7978step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7978step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

def raw7979 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7979step0 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7979step1 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7979step2 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7979step3 : Matrix (Fin 0) (Fin 0) ℤ := ![]

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

def raw7980 : Matrix (Fin 4) (Fin 1) ℤ := ![![0], ![0], ![0], ![0]]

def raw7980step0 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7980step1 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7980step2 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7980step3 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7980step4 : Matrix (Fin 0) (Fin 0) ℤ := ![]

theorem canonical7980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7980 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7980 = injectiveMoment H raw7980step0 := by
      have hz : ∀ j, raw7980 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7980step0 = (fun i j => raw7980 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980 permutation27 hz
    injectiveMoment H raw7980step0 = injectiveMoment H raw7980step1 := by
      have hz : ∀ j, raw7980step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7980step1 = (fun i j => raw7980step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step0 permutation7 hz
    injectiveMoment H raw7980step1 = injectiveMoment H raw7980step2 := by
      have hz : ∀ j, raw7980step1 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7980step2 = (fun i j => raw7980step1 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step1 permutation2 hz
    injectiveMoment H raw7980step2 = injectiveMoment H raw7980step3 := by
      have hz : ∀ j, raw7980step2 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7980step3 = (fun i j => raw7980step2 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step2 permutation0 hz
    injectiveMoment H raw7980step3 = injectiveMoment H raw7980step4 := by
      have hz : ∀ i, raw7980step3 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7980step4 = (fun i j => raw7980step3 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7980step3 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

def raw7981 : Matrix (Fin 5) (Fin 1) ℤ := ![![0], ![0], ![0], ![0], ![0]]

def raw7981step0 : Matrix (Fin 4) (Fin 1) ℤ := ![![0], ![0], ![0], ![0]]

def raw7981step1 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7981step2 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7981step3 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7981step4 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7981step5 : Matrix (Fin 0) (Fin 0) ℤ := ![]

theorem canonical7981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7981 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7981 = injectiveMoment H raw7981step0 := by
      have hz : ∀ j, raw7981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7981step0 = (fun i j => raw7981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981 permutation128 hz
    injectiveMoment H raw7981step0 = injectiveMoment H raw7981step1 := by
      have hz : ∀ j, raw7981step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7981step1 = (fun i j => raw7981step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step0 permutation27 hz
    injectiveMoment H raw7981step1 = injectiveMoment H raw7981step2 := by
      have hz : ∀ j, raw7981step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7981step2 = (fun i j => raw7981step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step1 permutation7 hz
    injectiveMoment H raw7981step2 = injectiveMoment H raw7981step3 := by
      have hz : ∀ j, raw7981step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7981step3 = (fun i j => raw7981step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step2 permutation2 hz
    injectiveMoment H raw7981step3 = injectiveMoment H raw7981step4 := by
      have hz : ∀ j, raw7981step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7981step4 = (fun i j => raw7981step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step3 permutation0 hz
    injectiveMoment H raw7981step4 = injectiveMoment H raw7981step5 := by
      have hz : ∀ i, raw7981step4 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7981step5 = (fun i j => raw7981step4 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7981step4 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

def raw7982 : Matrix (Fin 6) (Fin 1) ℤ := ![![0], ![0], ![0], ![0], ![0], ![0]]

def raw7982step0 : Matrix (Fin 5) (Fin 1) ℤ := ![![0], ![0], ![0], ![0], ![0]]

def raw7982step1 : Matrix (Fin 4) (Fin 1) ℤ := ![![0], ![0], ![0], ![0]]

def raw7982step2 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7982step3 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7982step4 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7982step5 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7982step6 : Matrix (Fin 0) (Fin 0) ℤ := ![]

theorem canonical7982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7982 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7982 = injectiveMoment H raw7982step0 := by
      have hz : ∀ j, raw7982 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7982step0 = (fun i j => raw7982 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982 permutation308 hz
    injectiveMoment H raw7982step0 = injectiveMoment H raw7982step1 := by
      have hz : ∀ j, raw7982step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7982step1 = (fun i j => raw7982step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step0 permutation128 hz
    injectiveMoment H raw7982step1 = injectiveMoment H raw7982step2 := by
      have hz : ∀ j, raw7982step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7982step2 = (fun i j => raw7982step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step1 permutation27 hz
    injectiveMoment H raw7982step2 = injectiveMoment H raw7982step3 := by
      have hz : ∀ j, raw7982step2 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7982step3 = (fun i j => raw7982step2 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step2 permutation7 hz
    injectiveMoment H raw7982step3 = injectiveMoment H raw7982step4 := by
      have hz : ∀ j, raw7982step3 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7982step4 = (fun i j => raw7982step3 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step3 permutation2 hz
    injectiveMoment H raw7982step4 = injectiveMoment H raw7982step5 := by
      have hz : ∀ j, raw7982step4 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7982step5 = (fun i j => raw7982step4 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step4 permutation0 hz
    injectiveMoment H raw7982step5 = injectiveMoment H raw7982step6 := by
      have hz : ∀ i, raw7982step5 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7982step6 = (fun i j => raw7982step5 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7982step5 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

def raw7983 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7983step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7983 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw7983 = injectiveMoment H raw7983step0 := by
      have heq : raw7983step0 = (fun i j => raw7983 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7983 permutation17 permutation4
    _ = injectiveMoment H node281 := by rfl

def raw7984 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![1, 2, -3]]

def raw7984step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-1, -2, 3]]

def raw7984step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical7984 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7984 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw7984 = injectiveMoment H raw7984step0 := by
      have heq : raw7984step0 = -raw7984 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7984).symm
    injectiveMoment H raw7984step0 = injectiveMoment H raw7984step1 := by
      have heq : raw7984step1 = (fun i j => raw7984step0 (permutation7 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7984step0 permutation7 permutation3
    _ = injectiveMoment H node59 := by rfl

def raw7985 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 3, -2], ![1, 1, -2]]

def raw7985step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical7985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7985 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw7985 = injectiveMoment H raw7985step0 := by
      have heq : raw7985step0 = (fun i j => raw7985 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7985 permutation5 permutation4
    _ = injectiveMoment H node59 := by rfl

def raw7986 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 4, -3], ![1, 0, -1]]

def raw7986step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7986 = injectiveMoment H node54 := by
  calc
    injectiveMoment H raw7986 = injectiveMoment H raw7986step0 := by
      have heq : raw7986step0 = (fun i j => raw7986 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7986 permutation5 permutation4
    _ = injectiveMoment H node54 := by rfl

def raw7987 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![0, 2, -2]]

def raw7987step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

theorem canonical7987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7987 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw7987 = injectiveMoment H raw7987step0 := by
      have hz : ∀ i, raw7987 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw7987step0 = (fun i j => raw7987 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7987 permutation3 hz
    _ = injectiveMoment H node9 := by rfl

def raw7988 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -4, 4], ![0, 4, -4]]

def raw7988step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

theorem canonical7988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7988 = injectiveMoment H node2 := by
  calc
    injectiveMoment H raw7988 = injectiveMoment H raw7988step0 := by
      have hz : ∀ i, raw7988 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw7988step0 = (fun i j => raw7988 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7988 permutation3 hz
    _ = injectiveMoment H node2 := by rfl

def raw7989 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 2, -3]]

def raw7989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -2, 3]]

def raw7989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

theorem canonical7989 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7989 = injectiveMoment H node265 := by
  calc
    injectiveMoment H raw7989 = injectiveMoment H raw7989step0 := by
      have heq : raw7989step0 = -raw7989 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7989).symm
    injectiveMoment H raw7989step0 = injectiveMoment H raw7989step1 := by
      have heq : raw7989step1 = (fun i j => raw7989step0 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7989step0 permutation31 permutation3
    _ = injectiveMoment H node265 := by rfl

def raw7990 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 1, -2]]

def raw7990step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

theorem canonical7990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7990 = injectiveMoment H node277 := by
  calc
    injectiveMoment H raw7990 = injectiveMoment H raw7990step0 := by
      have heq : raw7990step0 = (fun i j => raw7990 (permutation15 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7990 permutation15 permutation3
    _ = injectiveMoment H node277 := by rfl

def raw7991 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![0, 4, -4], ![1, 0, -1]]

def raw7991step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

theorem canonical7991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7991 = injectiveMoment H node278 := by
  calc
    injectiveMoment H raw7991 = injectiveMoment H raw7991step0 := by
      have heq : raw7991step0 = (fun i j => raw7991 (permutation15 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7991 permutation15 permutation3
    _ = injectiveMoment H node278 := by rfl

def raw7992 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7992 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7992 = injectiveMoment H node1293 := by
  calc
    injectiveMoment H raw7992 = injectiveMoment H raw7992step0 := by
      have heq : raw7992step0 = (fun i j => raw7992 (permutation64 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7992 permutation64 permutation4
    _ = injectiveMoment H node1293 := by rfl

def raw7993 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1]]

def raw7993step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7993 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7993 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw7993 = injectiveMoment H raw7993step0 := by
      have heq : raw7993step0 = (fun i j => raw7993 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7993 permutation17 permutation4
    _ = injectiveMoment H node292 := by rfl

def raw7994 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0]]

def raw7994step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7994 = injectiveMoment H node289 := by
  calc
    injectiveMoment H raw7994 = injectiveMoment H raw7994step0 := by
      have heq : raw7994step0 = (fun i j => raw7994 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7994 permutation17 permutation4
    _ = injectiveMoment H node289 := by rfl

def raw7995 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![1, 1, -2]]

def raw7995step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical7995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7995 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw7995 = injectiveMoment H raw7995step0 := by
      have heq : raw7995step0 = (fun i j => raw7995 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7995 permutation5 permutation4
    _ = injectiveMoment H node63 := by rfl

def raw7996 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![1, 0, -1]]

def raw7996step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7996 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7996 = injectiveMoment H raw7996step0 := by
      have heq : raw7996step0 = (fun i j => raw7996 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7996 permutation5 permutation4
    _ = injectiveMoment H node58 := by rfl

def raw7997 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 4, -3], ![1, -1, 0]]

def raw7997step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7997 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7997 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7997 = injectiveMoment H raw7997step0 := by
      have heq : raw7997step0 = (fun i j => raw7997 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7997 permutation5 permutation4
    _ = injectiveMoment H node53 := by rfl

def raw7998 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw7998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7998 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7998 = injectiveMoment H node1293 := by
  calc
    injectiveMoment H raw7998 = injectiveMoment H raw7998step0 := by
      have heq : raw7998step0 = (fun i j => raw7998 (permutation88 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7998 permutation88 permutation4
    _ = injectiveMoment H node1293 := by rfl

def raw7999 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1]]

def raw7999step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7999 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw7999 = injectiveMoment H raw7999step0 := by
      have heq : raw7999step0 = (fun i j => raw7999 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7999 permutation23 permutation4
    _ = injectiveMoment H node285 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
