import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9056 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def raw9056step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def raw9056step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def raw9056step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0]]

def raw9056step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![0, 0], ![0, 0]]

def raw9056step4 : Matrix (Fin 1) (Fin 2) ℤ := ![![0, 0]]

def raw9056step5 : Matrix (Fin 0) (Fin 2) ℤ := ![]

def raw9056step6 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw9056step7 : Matrix (Fin 0) (Fin 0) ℤ := ![]

theorem canonical9056 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9056 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw9056 = injectiveMoment H raw9056step0 := by
      have hz : ∀ j, raw9056 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9056step0 = (fun i j => raw9056 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9056 permutation308 hz
    injectiveMoment H raw9056step0 = injectiveMoment H raw9056step1 := by
      have hz : ∀ j, raw9056step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9056step1 = (fun i j => raw9056step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9056step0 permutation128 hz
    injectiveMoment H raw9056step1 = injectiveMoment H raw9056step2 := by
      have hz : ∀ j, raw9056step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw9056step2 = (fun i j => raw9056step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9056step1 permutation27 hz
    injectiveMoment H raw9056step2 = injectiveMoment H raw9056step3 := by
      have hz : ∀ j, raw9056step2 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw9056step3 = (fun i j => raw9056step2 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9056step2 permutation7 hz
    injectiveMoment H raw9056step3 = injectiveMoment H raw9056step4 := by
      have hz : ∀ j, raw9056step3 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw9056step4 = (fun i j => raw9056step3 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9056step3 permutation2 hz
    injectiveMoment H raw9056step4 = injectiveMoment H raw9056step5 := by
      have hz : ∀ j, raw9056step4 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw9056step5 = (fun i j => raw9056step4 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9056step4 permutation0 hz
    injectiveMoment H raw9056step5 = injectiveMoment H raw9056step6 := by
      have hz : ∀ i, raw9056step5 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw9056step6 = (fun i j => raw9056step5 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9056step5 permutation2 hz
    injectiveMoment H raw9056step6 = injectiveMoment H raw9056step7 := by
      have hz : ∀ i, raw9056step6 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw9056step7 = (fun i j => raw9056step6 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9056step6 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

def raw9057 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def raw9057step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def raw9057step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def raw9057step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def raw9057step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9057 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9057 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9057 = injectiveMoment H raw9057step0 := by
      have hz : ∀ j, raw9057 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9057step0 = (fun i j => raw9057 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9057 permutation104 hz
    injectiveMoment H raw9057step0 = injectiveMoment H raw9057step1 := by
      have hz : ∀ j, raw9057step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9057step1 = (fun i j => raw9057step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9057step0 permutation15 hz
    injectiveMoment H raw9057step1 = injectiveMoment H raw9057step2 := by
      have hz : ∀ j, raw9057step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9057step2 = (fun i j => raw9057step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9057step1 permutation3 hz
    injectiveMoment H raw9057step2 = injectiveMoment H raw9057step3 := by
      have heq : raw9057step3 = (fun i j => raw9057step2 (permutation2 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9057step2 permutation2 permutation1
    _ = injectiveMoment H node5 := by rfl

def raw9058 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1], ![0, 0], ![0, 0]]

def raw9058step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1], ![0, 0]]

def raw9058step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def raw9058step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def raw9058step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9058 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9058 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9058 = injectiveMoment H raw9058step0 := by
      have hz : ∀ j, raw9058 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9058step0 = (fun i j => raw9058 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9058 permutation128 hz
    injectiveMoment H raw9058step0 = injectiveMoment H raw9058step1 := by
      have hz : ∀ j, raw9058step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw9058step1 = (fun i j => raw9058step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9058step0 permutation27 hz
    injectiveMoment H raw9058step1 = injectiveMoment H raw9058step2 := by
      have hz : ∀ j, raw9058step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9058step2 = (fun i j => raw9058step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9058step1 permutation3 hz
    injectiveMoment H raw9058step2 = injectiveMoment H raw9058step3 := by
      have heq : raw9058step3 = (fun i j => raw9058step2 (permutation2 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9058step2 permutation2 permutation1
    _ = injectiveMoment H node5 := by rfl

def raw9059 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def raw9059step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def raw9059step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def raw9059step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def raw9059step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9059 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9059 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9059 = injectiveMoment H raw9059step0 := by
      have hz : ∀ j, raw9059 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9059step0 = (fun i j => raw9059 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9059 permutation104 hz
    injectiveMoment H raw9059step0 = injectiveMoment H raw9059step1 := by
      have hz : ∀ j, raw9059step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw9059step1 = (fun i j => raw9059step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9059step0 permutation21 hz
    injectiveMoment H raw9059step1 = injectiveMoment H raw9059step2 := by
      have hz : ∀ j, raw9059step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9059step2 = (fun i j => raw9059step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9059step1 permutation3 hz
    injectiveMoment H raw9059step2 = injectiveMoment H raw9059step3 := by
      have heq : raw9059step3 = (fun i j => raw9059step2 (permutation2 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9059step2 permutation2 permutation1
    _ = injectiveMoment H node5 := by rfl

def raw9060 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -4, 4], ![0, -1, 3, -2], ![0, 1, 1, -2]]

def raw9060step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 3, -2], ![1, 1, -2]]

def raw9060step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical9060 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9060 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw9060 = injectiveMoment H raw9060step0 := by
      have hz : ∀ i, raw9060 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9060step0 = (fun i j => raw9060 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9060 permutation9 hz
    injectiveMoment H raw9060step0 = injectiveMoment H raw9060step1 := by
      have heq : raw9060step1 = (fun i j => raw9060step0 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9060step0 permutation5 permutation4
    _ = injectiveMoment H node59 := by rfl

def raw9061 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

theorem canonical9061 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9061 = injectiveMoment H node2847 := by
  calc
    injectiveMoment H raw9061 = injectiveMoment H raw9061step0 := by
      have heq : raw9061step0 = (fun i j => raw9061 (permutation63 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9061 permutation63 permutation10
    _ = injectiveMoment H node2847 := by rfl

def raw9062 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw9062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

theorem canonical9062 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9062 = injectiveMoment H node1345 := by
  calc
    injectiveMoment H raw9062 = injectiveMoment H raw9062step0 := by
      have heq : raw9062step0 = (fun i j => raw9062 (permutation17 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9062 permutation17 permutation10
    _ = injectiveMoment H node1345 := by rfl

def raw9063 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw9063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-3, 1, 0, 2], ![3, -1, -1, -1]]

def raw9063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical9063 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9063 = injectiveMoment H node937 := by
  calc
    injectiveMoment H raw9063 = injectiveMoment H raw9063step0 := by
      have heq : raw9063step0 = raw9063.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9063).symm
    injectiveMoment H raw9063step0 = injectiveMoment H raw9063step1 := by
      have heq : raw9063step1 = (fun i j => raw9063step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9063step0 permutation28 permutation24
    _ = injectiveMoment H node937 := by rfl

def raw9064 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-3, 2, 0, 1], ![3, -2, -1, 0]]

def raw9064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical9064 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9064 = injectiveMoment H node1231 := by
  calc
    injectiveMoment H raw9064 = injectiveMoment H raw9064step0 := by
      have heq : raw9064step0 = raw9064.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9064).symm
    injectiveMoment H raw9064step0 = injectiveMoment H raw9064step1 := by
      have heq : raw9064step1 = (fun i j => raw9064step0 (permutation28 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9064step0 permutation28 permutation26
    _ = injectiveMoment H node1231 := by rfl

def raw9065 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 2, 2, -3], ![1, -2, 1, 0]]

def raw9065step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-3, 2, 1], ![3, -3, 0]]

def raw9065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical9065 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9065 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw9065 = injectiveMoment H raw9065step0 := by
      have heq : raw9065step0 = raw9065.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9065).symm
    injectiveMoment H raw9065step0 = injectiveMoment H raw9065step1 := by
      have heq : raw9065step1 = (fun i j => raw9065step0 (permutation20 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9065step0 permutation20 permutation7
    _ = injectiveMoment H node214 := by rfl

def raw9066 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 2, 3, -4], ![1, -2, 0, 1]]

def raw9066step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-3, 3, 0], ![3, -4, 1]]

def raw9066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

theorem canonical9066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9066 = injectiveMoment H node195 := by
  calc
    injectiveMoment H raw9066 = injectiveMoment H raw9066step0 := by
      have heq : raw9066step0 = raw9066.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9066).symm
    injectiveMoment H raw9066step0 = injectiveMoment H raw9066step1 := by
      have heq : raw9066step1 = (fun i j => raw9066step0 (permutation17 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9066step0 permutation17 permutation7
    _ = injectiveMoment H node195 := by rfl

def raw9067 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, -2, 1, 1], ![0, 2, 2, -4]]

def raw9067step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, 2, -1, -1], ![0, -2, -2, 4]]

def raw9067step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, -2, 4]]

def raw9067step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9067 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9067 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw9067 = injectiveMoment H raw9067step0 := by
      have heq : raw9067step0 = -raw9067 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9067).symm
    injectiveMoment H raw9067step0 = injectiveMoment H raw9067step1 := by
      have hz : ∀ i, raw9067step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9067step1 = (fun i j => raw9067step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9067step0 permutation9 hz
    injectiveMoment H raw9067step1 = injectiveMoment H raw9067step2 := by
      have heq : raw9067step2 = (fun i j => raw9067step1 (permutation7 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9067step1 permutation7 permutation3
    _ = injectiveMoment H node32 := by rfl

def raw9068 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, -2, 2, 0], ![0, 2, 1, -3]]

def raw9068step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, 2, -2, 0], ![0, -2, -1, 3]]

def raw9068step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]

def raw9068step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical9068 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9068 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw9068 = injectiveMoment H raw9068step0 := by
      have heq : raw9068step0 = -raw9068 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9068).symm
    injectiveMoment H raw9068step0 = injectiveMoment H raw9068step1 := by
      have hz : ∀ i, raw9068step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9068step1 = (fun i j => raw9068step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9068step0 permutation9 hz
    injectiveMoment H raw9068step1 = injectiveMoment H raw9068step2 := by
      have heq : raw9068step2 = (fun i j => raw9068step1 (permutation7 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9068step1 permutation7 permutation3
    _ = injectiveMoment H node37 := by rfl

def raw9069 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, -2, 3, -1], ![0, 2, 0, -2]]

def raw9069step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 3, -1], ![2, 0, -2]]

def raw9069step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical9069 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9069 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw9069 = injectiveMoment H raw9069step0 := by
      have hz : ∀ i, raw9069 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9069step0 = (fun i j => raw9069 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9069 permutation9 hz
    injectiveMoment H raw9069step0 = injectiveMoment H raw9069step1 := by
      have heq : raw9069step1 = (fun i j => raw9069step0 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9069step0 permutation5 permutation4
    _ = injectiveMoment H node37 := by rfl

def raw9070 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, -1, 2, -1], ![0, 1, 1, -2]]

def raw9070step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![1, 1, -2]]

def raw9070step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical9070 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9070 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw9070 = injectiveMoment H raw9070step0 := by
      have hz : ∀ i, raw9070 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9070step0 = (fun i j => raw9070 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9070 permutation9 hz
    injectiveMoment H raw9070step0 = injectiveMoment H raw9070step1 := by
      have heq : raw9070step1 = (fun i j => raw9070step0 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9070step0 permutation5 permutation4
    _ = injectiveMoment H node63 := by rfl

def raw9071 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9071step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

theorem canonical9071 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9071 = injectiveMoment H node2847 := by
  calc
    injectiveMoment H raw9071 = injectiveMoment H raw9071step0 := by
      have heq : raw9071step0 = (fun i j => raw9071 (permutation86 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9071 permutation86 permutation10
    _ = injectiveMoment H node2847 := by rfl

def raw9072 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -2, 2, -1]]

def raw9072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-3, 1, 0, 2], ![3, -1, -1, -1]]

def raw9072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem canonical9072 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9072 = injectiveMoment H node938 := by
  calc
    injectiveMoment H raw9072 = injectiveMoment H raw9072step0 := by
      have heq : raw9072step0 = raw9072.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9072).symm
    injectiveMoment H raw9072step0 = injectiveMoment H raw9072step1 := by
      have heq : raw9072step1 = (fun i j => raw9072step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9072step0 permutation27 permutation18
    _ = injectiveMoment H node938 := by rfl

def raw9073 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -2, 1, 0]]

def raw9073step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, 0, 1]]

theorem canonical9073 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9073 = injectiveMoment H node2861 := by
  calc
    injectiveMoment H raw9073 = injectiveMoment H raw9073step0 := by
      have heq : raw9073step0 = (fun i j => raw9073 (permutation112 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9073 permutation112 permutation10
    _ = injectiveMoment H node2861 := by rfl

def raw9074 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -1, 1, 0]]

def raw9074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0]]

def raw9074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical9074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9074 = injectiveMoment H node1293 := by
  calc
    injectiveMoment H raw9074 = injectiveMoment H raw9074step0 := by
      have hz : ∀ i, raw9074 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9074step0 = (fun i j => raw9074 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9074 permutation9 hz
    injectiveMoment H raw9074step0 = injectiveMoment H raw9074step1 := by
      have heq : raw9074step1 = (fun i j => raw9074step0 (permutation135 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9074step0 permutation135 permutation4
    _ = injectiveMoment H node1293 := by rfl

def raw9075 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -1, 2, -1]]

def raw9075step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1]]

def raw9075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical9075 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9075 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw9075 = injectiveMoment H raw9075step0 := by
      have hz : ∀ i, raw9075 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9075step0 = (fun i j => raw9075 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9075 permutation9 hz
    injectiveMoment H raw9075step0 = injectiveMoment H raw9075step1 := by
      have heq : raw9075step1 = (fun i j => raw9075step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9075step0 permutation29 permutation4
    _ = injectiveMoment H node285 := by rfl

def raw9076 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -2, 1, 0]]

def raw9076step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

theorem canonical9076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9076 = injectiveMoment H node1374 := by
  calc
    injectiveMoment H raw9076 = injectiveMoment H raw9076step0 := by
      have heq : raw9076step0 = (fun i j => raw9076 (permutation23 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9076 permutation23 permutation10
    _ = injectiveMoment H node1374 := by rfl

def raw9077 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, -1, 1, 0]]

def raw9077step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![-1, 1, 0]]

def raw9077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical9077 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9077 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw9077 = injectiveMoment H raw9077step0 := by
      have hz : ∀ i, raw9077 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9077step0 = (fun i j => raw9077 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9077 permutation9 hz
    injectiveMoment H raw9077step0 = injectiveMoment H raw9077step1 := by
      have heq : raw9077step1 = (fun i j => raw9077step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9077step0 permutation29 permutation4
    _ = injectiveMoment H node292 := by rfl

def raw9078 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 1, 2, -3], ![0, -1, 1, 0]]

def raw9078step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, -1, -2, 3], ![0, 1, -1, 0]]

def raw9078step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![-1, -2, 3], ![1, -1, 0]]

def raw9078step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical9078 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9078 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw9078 = injectiveMoment H raw9078step0 := by
      have heq : raw9078step0 = -raw9078 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9078).symm
    injectiveMoment H raw9078step0 = injectiveMoment H raw9078step1 := by
      have hz : ∀ i, raw9078step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9078step1 = (fun i j => raw9078step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9078step0 permutation9 hz
    injectiveMoment H raw9078step1 = injectiveMoment H raw9078step2 := by
      have heq : raw9078step2 = (fun i j => raw9078step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9078step1 permutation5 permutation3
    _ = injectiveMoment H node58 := by rfl

def raw9079 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 1, 3, -4], ![0, -1, 0, 1]]

def raw9079step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, -1, -3, 4], ![0, 1, 0, -1]]

def raw9079step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![-1, -3, 4], ![1, 0, -1]]

def raw9079step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical9079 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9079 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw9079 = injectiveMoment H raw9079step0 := by
      have heq : raw9079step0 = -raw9079 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9079).symm
    injectiveMoment H raw9079step0 = injectiveMoment H raw9079step1 := by
      have hz : ∀ i, raw9079step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9079step1 = (fun i j => raw9079step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9079step0 permutation9 hz
    injectiveMoment H raw9079step1 = injectiveMoment H raw9079step2 := by
      have heq : raw9079step2 = (fun i j => raw9079step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9079step1 permutation5 permutation3
    _ = injectiveMoment H node53 := by rfl

def raw9080 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 2, 2, -4], ![0, -2, 1, 1]]

def raw9080step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, -2, -2, 4], ![0, 2, -1, -1]]

def raw9080step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![-2, -2, 4], ![2, -1, -1]]

def raw9080step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9080 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9080 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw9080 = injectiveMoment H raw9080step0 := by
      have heq : raw9080step0 = -raw9080 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9080).symm
    injectiveMoment H raw9080step0 = injectiveMoment H raw9080step1 := by
      have hz : ∀ i, raw9080step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9080step1 = (fun i j => raw9080step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9080step0 permutation9 hz
    injectiveMoment H raw9080step1 = injectiveMoment H raw9080step2 := by
      have heq : raw9080step2 = (fun i j => raw9080step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9080step1 permutation5 permutation3
    _ = injectiveMoment H node32 := by rfl

def raw9081 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 0, 0, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw9081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-2, 0, 2, 0], ![2, 1, -4, 1]]

def raw9081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![2, 0, -2, 0], ![-2, -1, 4, -1]]

def raw9081step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical9081 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9081 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw9081 = injectiveMoment H raw9081step0 := by
      have heq : raw9081step0 = raw9081.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9081).symm
    injectiveMoment H raw9081step0 = injectiveMoment H raw9081step1 := by
      have heq : raw9081step1 = -raw9081step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9081step0).symm
    injectiveMoment H raw9081step1 = injectiveMoment H raw9081step2 := by
      have heq : raw9081step2 = (fun i j => raw9081step1 (permutation30 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9081step1 permutation30 permutation16
    _ = injectiveMoment H node775 := by rfl

def raw9082 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw9082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-2, 1, 0, 1], ![2, 0, -1, -1]]

def raw9082step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical9082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9082 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw9082 = injectiveMoment H raw9082step0 := by
      have heq : raw9082step0 = raw9082.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9082).symm
    injectiveMoment H raw9082step0 = injectiveMoment H raw9082step1 := by
      have heq : raw9082step1 = (fun i j => raw9082step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9082step0 permutation28 permutation24
    _ = injectiveMoment H node1242 := by rfl

def raw9083 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw9083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem canonical9083 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9083 = injectiveMoment H node1344 := by
  calc
    injectiveMoment H raw9083 = injectiveMoment H raw9083step0 := by
      have heq : raw9083step0 = (fun i j => raw9083 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9083 permutation15 permutation9
    _ = injectiveMoment H node1344 := by rfl

def raw9084 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw9084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

theorem canonical9084 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9084 = injectiveMoment H node1345 := by
  calc
    injectiveMoment H raw9084 = injectiveMoment H raw9084step0 := by
      have heq : raw9084step0 = (fun i j => raw9084 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9084 permutation15 permutation9
    _ = injectiveMoment H node1345 := by rfl

def raw9085 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw9085step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-2, -1, 0, 3], ![2, 1, -1, -2]]

def raw9085step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, -1, 2], ![2, 1, 0, -3], ![-2, -1, 1, 2]]

def raw9085step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical9085 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9085 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw9085 = injectiveMoment H raw9085step0 := by
      have heq : raw9085step0 = raw9085.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9085).symm
    injectiveMoment H raw9085step0 = injectiveMoment H raw9085step1 := by
      have heq : raw9085step1 = -raw9085step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9085step0).symm
    injectiveMoment H raw9085step1 = injectiveMoment H raw9085step2 := by
      have heq : raw9085step2 = (fun i j => raw9085step1 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9085step1 permutation15 permutation23
    _ = injectiveMoment H node1083 := by rfl

def raw9086 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, 0, 0], ![1, -1, 2, -2]]

def raw9086step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 0, 2], ![2, 0, -2]]

def raw9086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical9086 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9086 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw9086 = injectiveMoment H raw9086step0 := by
      have heq : raw9086step0 = raw9086.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9086).symm
    injectiveMoment H raw9086step0 = injectiveMoment H raw9086step1 := by
      have heq : raw9086step1 = (fun i j => raw9086step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9086step0 permutation12 permutation5
    _ = injectiveMoment H node291 := by rfl

def raw9087 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw9087step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw9087step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical9087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9087 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw9087 = injectiveMoment H raw9087step0 := by
      have heq : raw9087step0 = raw9087.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9087).symm
    injectiveMoment H raw9087step0 = injectiveMoment H raw9087step1 := by
      have heq : raw9087step1 = (fun i j => raw9087step0 (permutation29 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9087step0 permutation29 permutation26
    _ = injectiveMoment H node1241 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
