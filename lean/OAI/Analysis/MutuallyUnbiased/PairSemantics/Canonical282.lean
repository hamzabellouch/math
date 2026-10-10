import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9024 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw9024step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9024step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9024step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9024 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9024 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9024 = injectiveMoment H raw9024step0 := by
      have hz : ∀ j, raw9024 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw9024step0 = (fun i j => raw9024 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9024 permutation258 hz
    injectiveMoment H raw9024step0 = injectiveMoment H raw9024step1 := by
      have hz : ∀ j, raw9024step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9024step1 = (fun i j => raw9024step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9024step0 permutation33 hz
    injectiveMoment H raw9024step1 = injectiveMoment H raw9024step2 := by
      have heq : raw9024step2 = (fun i j => raw9024step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9024step1 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw9025 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9025step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9025step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9025 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9025 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9025 = injectiveMoment H raw9025step0 := by
      have hz : ∀ j, raw9025 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9025step0 = (fun i j => raw9025 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9025 permutation33 hz
    injectiveMoment H raw9025step0 = injectiveMoment H raw9025step1 := by
      have heq : raw9025step1 = (fun i j => raw9025step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9025step0 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw9026 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0]]

def raw9026step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9026step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9026step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9026 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9026 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9026 = injectiveMoment H raw9026step0 := by
      have hz : ∀ j, raw9026 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9026step0 = (fun i j => raw9026 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9026 permutation308 hz
    injectiveMoment H raw9026step0 = injectiveMoment H raw9026step1 := by
      have hz : ∀ j, raw9026step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9026step1 = (fun i j => raw9026step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9026step0 permutation33 hz
    injectiveMoment H raw9026step1 = injectiveMoment H raw9026step2 := by
      have heq : raw9026step2 = (fun i j => raw9026step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9026step1 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw9027 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def raw9027step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9027step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9027 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9027 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9027 = injectiveMoment H raw9027step0 := by
      have hz : ∀ j, raw9027 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw9027step0 = (fun i j => raw9027 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9027 permutation27 hz
    injectiveMoment H raw9027step0 = injectiveMoment H raw9027step1 := by
      have hz : ∀ j, raw9027step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9027step1 = (fun i j => raw9027step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9027step0 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9028 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def raw9028step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def raw9028step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9028step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9028 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9028 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9028 = injectiveMoment H raw9028step0 := by
      have hz : ∀ j, raw9028 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9028step0 = (fun i j => raw9028 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9028 permutation128 hz
    injectiveMoment H raw9028step0 = injectiveMoment H raw9028step1 := by
      have hz : ∀ j, raw9028step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw9028step1 = (fun i j => raw9028step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9028step0 permutation27 hz
    injectiveMoment H raw9028step1 = injectiveMoment H raw9028step2 := by
      have hz : ∀ j, raw9028step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9028step2 = (fun i j => raw9028step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9028step1 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9029 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![0, 0]]

def raw9029step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def raw9029step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def raw9029step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9029step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9029 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9029 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9029 = injectiveMoment H raw9029step0 := by
      have hz : ∀ j, raw9029 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9029step0 = (fun i j => raw9029 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9029 permutation308 hz
    injectiveMoment H raw9029step0 = injectiveMoment H raw9029step1 := by
      have hz : ∀ j, raw9029step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9029step1 = (fun i j => raw9029step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9029step0 permutation128 hz
    injectiveMoment H raw9029step1 = injectiveMoment H raw9029step2 := by
      have hz : ∀ j, raw9029step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw9029step2 = (fun i j => raw9029step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9029step1 permutation27 hz
    injectiveMoment H raw9029step2 = injectiveMoment H raw9029step3 := by
      have hz : ∀ j, raw9029step2 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9029step3 = (fun i j => raw9029step2 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9029step2 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9030 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw9030step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw9030step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9030 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9030 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9030 = injectiveMoment H raw9030step0 := by
      have hz : ∀ j, raw9030 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9030step0 = (fun i j => raw9030 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9030 permutation33 hz
    injectiveMoment H raw9030step0 = injectiveMoment H raw9030step1 := by
      have heq : raw9030step1 = (fun i j => raw9030step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9030step0 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw9031 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw9031step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw9031step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw9031step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9031 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9031 = injectiveMoment H raw9031step0 := by
      have hz : ∀ j, raw9031 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw9031step0 = (fun i j => raw9031 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9031 permutation258 hz
    injectiveMoment H raw9031step0 = injectiveMoment H raw9031step1 := by
      have hz : ∀ j, raw9031step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9031step1 = (fun i j => raw9031step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9031step0 permutation33 hz
    injectiveMoment H raw9031step1 = injectiveMoment H raw9031step2 := by
      have heq : raw9031step2 = (fun i j => raw9031step1 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9031step1 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw9032 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![-1, 1]]

def raw9032step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw9032step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9032 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9032 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9032 = injectiveMoment H raw9032step0 := by
      have hz : ∀ j, raw9032 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9032step0 = (fun i j => raw9032 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9032 permutation9 hz
    injectiveMoment H raw9032step0 = injectiveMoment H raw9032step1 := by
      have heq : raw9032step1 = (fun i j => raw9032step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9032step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9033 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw9033step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![-1, 1]]

def raw9033step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw9033step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9033 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9033 = injectiveMoment H raw9033step0 := by
      have hz : ∀ j, raw9033 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9033step0 = (fun i j => raw9033 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9033 permutation128 hz
    injectiveMoment H raw9033step0 = injectiveMoment H raw9033step1 := by
      have hz : ∀ j, raw9033step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9033step1 = (fun i j => raw9033step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9033step0 permutation9 hz
    injectiveMoment H raw9033step1 = injectiveMoment H raw9033step2 := by
      have heq : raw9033step2 = (fun i j => raw9033step1 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9033step1 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9034 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def raw9034step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![-1, 1]]

def raw9034step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw9034step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9034 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9034 = injectiveMoment H raw9034step0 := by
      have hz : ∀ j, raw9034 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9034step0 = (fun i j => raw9034 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9034 permutation104 hz
    injectiveMoment H raw9034step0 = injectiveMoment H raw9034step1 := by
      have hz : ∀ j, raw9034step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9034step1 = (fun i j => raw9034step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9034step0 permutation9 hz
    injectiveMoment H raw9034step1 = injectiveMoment H raw9034step2 := by
      have heq : raw9034step2 = (fun i j => raw9034step1 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9034step1 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9035 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw9035step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw9035step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![2, -2]]

def raw9035step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw9035step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical9035 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9035 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw9035 = injectiveMoment H raw9035step0 := by
      have hz : ∀ j, raw9035 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw9035step0 = (fun i j => raw9035 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9035 permutation258 hz
    injectiveMoment H raw9035step0 = injectiveMoment H raw9035step1 := by
      have hz : ∀ j, raw9035step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9035step1 = (fun i j => raw9035step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9035step0 permutation104 hz
    injectiveMoment H raw9035step1 = injectiveMoment H raw9035step2 := by
      have hz : ∀ j, raw9035step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9035step2 = (fun i j => raw9035step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9035step1 permutation15 hz
    injectiveMoment H raw9035step2 = injectiveMoment H raw9035step3 := by
      have hz : ∀ j, raw9035step2 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9035step3 = (fun i j => raw9035step2 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9035step2 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw9036 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw9036step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![2, -2]]

def raw9036step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw9036step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical9036 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9036 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw9036 = injectiveMoment H raw9036step0 := by
      have hz : ∀ j, raw9036 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9036step0 = (fun i j => raw9036 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9036 permutation104 hz
    injectiveMoment H raw9036step0 = injectiveMoment H raw9036step1 := by
      have hz : ∀ j, raw9036step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9036step1 = (fun i j => raw9036step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9036step0 permutation15 hz
    injectiveMoment H raw9036step1 = injectiveMoment H raw9036step2 := by
      have hz : ∀ j, raw9036step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9036step2 = (fun i j => raw9036step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9036step1 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw9037 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw9037step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw9037step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw9037step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical9037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9037 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw9037 = injectiveMoment H raw9037step0 := by
      have hz : ∀ j, raw9037 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9037step0 = (fun i j => raw9037 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9037 permutation202 hz
    injectiveMoment H raw9037step0 = injectiveMoment H raw9037step1 := by
      have hz : ∀ j, raw9037step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9037step1 = (fun i j => raw9037step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9037step0 permutation33 hz
    injectiveMoment H raw9037step1 = injectiveMoment H raw9037step2 := by
      have heq : raw9037step2 = (fun i j => raw9037step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9037step1 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw9038 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw9038step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9038step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9038step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9038 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9038 = injectiveMoment H raw9038step0 := by
      have hz : ∀ j, raw9038 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw9038step0 = (fun i j => raw9038 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9038 permutation258 hz
    injectiveMoment H raw9038step0 = injectiveMoment H raw9038step1 := by
      have hz : ∀ j, raw9038step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw9038step1 = (fun i j => raw9038step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9038step0 permutation57 hz
    injectiveMoment H raw9038step1 = injectiveMoment H raw9038step2 := by
      have hz : ∀ j, raw9038step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9038step2 = (fun i j => raw9038step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9038step1 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

def raw9039 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9039step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9039step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9039 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9039 = injectiveMoment H raw9039step0 := by
      have hz : ∀ j, raw9039 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw9039step0 = (fun i j => raw9039 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9039 permutation57 hz
    injectiveMoment H raw9039step0 = injectiveMoment H raw9039step1 := by
      have hz : ∀ j, raw9039step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9039step1 = (fun i j => raw9039step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9039step0 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

def raw9040 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw9040step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9040step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9040step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9040 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9040 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9040 = injectiveMoment H raw9040step0 := by
      have hz : ∀ j, raw9040 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9040step0 = (fun i j => raw9040 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9040 permutation308 hz
    injectiveMoment H raw9040step0 = injectiveMoment H raw9040step1 := by
      have hz : ∀ j, raw9040step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw9040step1 = (fun i j => raw9040step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9040step0 permutation57 hz
    injectiveMoment H raw9040step1 = injectiveMoment H raw9040step2 := by
      have hz : ∀ j, raw9040step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9040step2 = (fun i j => raw9040step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9040step1 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

def raw9041 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![2, -2], ![0, 0]]

def raw9041step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![2, -2]]

def raw9041step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw9041step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical9041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9041 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw9041 = injectiveMoment H raw9041step0 := by
      have hz : ∀ j, raw9041 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9041step0 = (fun i j => raw9041 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9041 permutation128 hz
    injectiveMoment H raw9041step0 = injectiveMoment H raw9041step1 := by
      have hz : ∀ j, raw9041step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9041step1 = (fun i j => raw9041step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9041step0 permutation15 hz
    injectiveMoment H raw9041step1 = injectiveMoment H raw9041step2 := by
      have hz : ∀ j, raw9041step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9041step2 = (fun i j => raw9041step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9041step1 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw9042 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw9042step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw9042step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw9042step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical9042 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9042 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw9042 = injectiveMoment H raw9042step0 := by
      have hz : ∀ j, raw9042 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9042step0 = (fun i j => raw9042 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9042 permutation202 hz
    injectiveMoment H raw9042step0 = injectiveMoment H raw9042step1 := by
      have hz : ∀ j, raw9042step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9042step1 = (fun i j => raw9042step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9042step0 permutation33 hz
    injectiveMoment H raw9042step1 = injectiveMoment H raw9042step2 := by
      have heq : raw9042step2 = (fun i j => raw9042step1 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9042step1 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw9043 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw9043step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9043step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9043step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9043step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9043 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9043 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9043 = injectiveMoment H raw9043step0 := by
      have hz : ∀ j, raw9043 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw9043step0 = (fun i j => raw9043 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9043 permutation258 hz
    injectiveMoment H raw9043step0 = injectiveMoment H raw9043step1 := by
      have hz : ∀ j, raw9043step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw9043step1 = (fun i j => raw9043step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9043step0 permutation57 hz
    injectiveMoment H raw9043step1 = injectiveMoment H raw9043step2 := by
      have hz : ∀ j, raw9043step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9043step2 = (fun i j => raw9043step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9043step1 permutation9 hz
    injectiveMoment H raw9043step2 = injectiveMoment H raw9043step3 := by
      have heq : raw9043step3 = (fun i j => raw9043step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9043step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9044 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9044step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9044step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9044 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9044 = injectiveMoment H raw9044step0 := by
      have hz : ∀ j, raw9044 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9044step0 = (fun i j => raw9044 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9044 permutation202 hz
    injectiveMoment H raw9044step0 = injectiveMoment H raw9044step1 := by
      have hz : ∀ j, raw9044step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9044step1 = (fun i j => raw9044step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9044step0 permutation33 hz
    _ = injectiveMoment H node65 := by rfl

def raw9045 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9045step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9045step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9045step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9045 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9045 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9045 = injectiveMoment H raw9045step0 := by
      have hz : ∀ j, raw9045 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw9045step0 = (fun i j => raw9045 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9045 permutation57 hz
    injectiveMoment H raw9045step0 = injectiveMoment H raw9045step1 := by
      have hz : ∀ j, raw9045step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9045step1 = (fun i j => raw9045step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9045step0 permutation9 hz
    injectiveMoment H raw9045step1 = injectiveMoment H raw9045step2 := by
      have heq : raw9045step2 = (fun i j => raw9045step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9045step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9046 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw9046step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9046step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9046step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9046step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9046 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9046 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9046 = injectiveMoment H raw9046step0 := by
      have hz : ∀ j, raw9046 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9046step0 = (fun i j => raw9046 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9046 permutation308 hz
    injectiveMoment H raw9046step0 = injectiveMoment H raw9046step1 := by
      have hz : ∀ j, raw9046step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw9046step1 = (fun i j => raw9046step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9046step0 permutation57 hz
    injectiveMoment H raw9046step1 = injectiveMoment H raw9046step2 := by
      have hz : ∀ j, raw9046step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9046step2 = (fun i j => raw9046step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9046step1 permutation9 hz
    injectiveMoment H raw9046step2 = injectiveMoment H raw9046step3 := by
      have heq : raw9046step3 = (fun i j => raw9046step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9046step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9047 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw9047step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9047step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9047step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9047step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9047 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9047 = injectiveMoment H raw9047step0 := by
      have hz : ∀ j, raw9047 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw9047step0 = (fun i j => raw9047 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9047 permutation241 hz
    injectiveMoment H raw9047step0 = injectiveMoment H raw9047step1 := by
      have hz : ∀ j, raw9047step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw9047step1 = (fun i j => raw9047step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9047step0 permutation57 hz
    injectiveMoment H raw9047step1 = injectiveMoment H raw9047step2 := by
      have hz : ∀ j, raw9047step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9047step2 = (fun i j => raw9047step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9047step1 permutation9 hz
    injectiveMoment H raw9047step2 = injectiveMoment H raw9047step3 := by
      have heq : raw9047step3 = (fun i j => raw9047step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9047step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9048 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![1, -1]]

def raw9048step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def raw9048step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9048step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9048 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9048 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9048 = injectiveMoment H raw9048step0 := by
      have hz : ∀ j, raw9048 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9048step0 = (fun i j => raw9048 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9048 permutation104 hz
    injectiveMoment H raw9048step0 = injectiveMoment H raw9048step1 := by
      have hz : ∀ j, raw9048step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9048step1 = (fun i j => raw9048step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9048step0 permutation15 hz
    injectiveMoment H raw9048step1 = injectiveMoment H raw9048step2 := by
      have hz : ∀ j, raw9048step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9048step2 = (fun i j => raw9048step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9048step1 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9049 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def raw9049step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9049step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9049 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9049 = injectiveMoment H raw9049step0 := by
      have hz : ∀ j, raw9049 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9049step0 = (fun i j => raw9049 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9049 permutation15 hz
    injectiveMoment H raw9049step0 = injectiveMoment H raw9049step1 := by
      have hz : ∀ j, raw9049step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9049step1 = (fun i j => raw9049step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9049step0 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9050 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9050step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9050step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9050step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9050 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9050 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9050 = injectiveMoment H raw9050step0 := by
      have hz : ∀ j, raw9050 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9050step0 = (fun i j => raw9050 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9050 permutation202 hz
    injectiveMoment H raw9050step0 = injectiveMoment H raw9050step1 := by
      have hz : ∀ j, raw9050step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9050step1 = (fun i j => raw9050step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9050step0 permutation33 hz
    injectiveMoment H raw9050step1 = injectiveMoment H raw9050step2 := by
      have heq : raw9050step2 = (fun i j => raw9050step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9050step1 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw9051 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def raw9051step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def raw9051step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9051step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9051 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9051 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9051 = injectiveMoment H raw9051step0 := by
      have hz : ∀ j, raw9051 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9051step0 = (fun i j => raw9051 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9051 permutation128 hz
    injectiveMoment H raw9051step0 = injectiveMoment H raw9051step1 := by
      have hz : ∀ j, raw9051step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9051step1 = (fun i j => raw9051step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9051step0 permutation15 hz
    injectiveMoment H raw9051step1 = injectiveMoment H raw9051step2 := by
      have hz : ∀ j, raw9051step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9051step2 = (fun i j => raw9051step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9051step1 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9052 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def raw9052step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def raw9052step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def raw9052step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9052step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9052 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9052 = injectiveMoment H raw9052step0 := by
      have hz : ∀ j, raw9052 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9052step0 = (fun i j => raw9052 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9052 permutation308 hz
    injectiveMoment H raw9052step0 = injectiveMoment H raw9052step1 := by
      have hz : ∀ j, raw9052step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9052step1 = (fun i j => raw9052step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9052step0 permutation128 hz
    injectiveMoment H raw9052step1 = injectiveMoment H raw9052step2 := by
      have hz : ∀ j, raw9052step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9052step2 = (fun i j => raw9052step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9052step1 permutation15 hz
    injectiveMoment H raw9052step2 = injectiveMoment H raw9052step3 := by
      have hz : ∀ j, raw9052step2 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9052step3 = (fun i j => raw9052step2 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9052step2 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9053 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![2, -2], ![-1, 1]]

def raw9053step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![-1, 1]]

def raw9053step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw9053step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9053 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9053 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9053 = injectiveMoment H raw9053step0 := by
      have hz : ∀ j, raw9053 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw9053step0 = (fun i j => raw9053 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9053 permutation57 hz
    injectiveMoment H raw9053step0 = injectiveMoment H raw9053step1 := by
      have hz : ∀ j, raw9053step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9053step1 = (fun i j => raw9053step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9053step0 permutation9 hz
    injectiveMoment H raw9053step1 = injectiveMoment H raw9053step2 := by
      have heq : raw9053step2 = (fun i j => raw9053step1 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9053step1 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9054 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def raw9054step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def raw9054step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9054step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9054 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9054 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9054 = injectiveMoment H raw9054step0 := by
      have hz : ∀ j, raw9054 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw9054step0 = (fun i j => raw9054 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9054 permutation80 hz
    injectiveMoment H raw9054step0 = injectiveMoment H raw9054step1 := by
      have hz : ∀ j, raw9054step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9054step1 = (fun i j => raw9054step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9054step0 permutation15 hz
    injectiveMoment H raw9054step1 = injectiveMoment H raw9054step2 := by
      have hz : ∀ j, raw9054step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9054step2 = (fun i j => raw9054step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9054step1 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9055 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def raw9055step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def raw9055step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0]]

def raw9055step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![0, 0], ![0, 0]]

def raw9055step3 : Matrix (Fin 1) (Fin 2) ℤ := ![![0, 0]]

def raw9055step4 : Matrix (Fin 0) (Fin 2) ℤ := ![]

def raw9055step5 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw9055step6 : Matrix (Fin 0) (Fin 0) ℤ := ![]

theorem canonical9055 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9055 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw9055 = injectiveMoment H raw9055step0 := by
      have hz : ∀ j, raw9055 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9055step0 = (fun i j => raw9055 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9055 permutation128 hz
    injectiveMoment H raw9055step0 = injectiveMoment H raw9055step1 := by
      have hz : ∀ j, raw9055step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw9055step1 = (fun i j => raw9055step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9055step0 permutation27 hz
    injectiveMoment H raw9055step1 = injectiveMoment H raw9055step2 := by
      have hz : ∀ j, raw9055step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw9055step2 = (fun i j => raw9055step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9055step1 permutation7 hz
    injectiveMoment H raw9055step2 = injectiveMoment H raw9055step3 := by
      have hz : ∀ j, raw9055step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw9055step3 = (fun i j => raw9055step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9055step2 permutation2 hz
    injectiveMoment H raw9055step3 = injectiveMoment H raw9055step4 := by
      have hz : ∀ j, raw9055step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw9055step4 = (fun i j => raw9055step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9055step3 permutation0 hz
    injectiveMoment H raw9055step4 = injectiveMoment H raw9055step5 := by
      have hz : ∀ i, raw9055step4 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw9055step5 = (fun i j => raw9055step4 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9055step4 permutation2 hz
    injectiveMoment H raw9055step5 = injectiveMoment H raw9055step6 := by
      have hz : ∀ i, raw9055step5 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw9055step6 = (fun i j => raw9055step5 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9055step5 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
