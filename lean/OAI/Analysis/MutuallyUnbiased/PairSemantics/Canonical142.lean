import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4544 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4544step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-1, 0, -1, 2, 0], ![2, 0, 0, -1, -1]]

def raw4544step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 2, 0], ![2, 0, -1, -1]]

def raw4544step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical4544 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4544 = injectiveMoment H node1244 := by
  calc
    injectiveMoment H raw4544 = injectiveMoment H raw4544step0 := by
      have heq : raw4544step0 = raw4544.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4544).symm
    injectiveMoment H raw4544step0 = injectiveMoment H raw4544step1 := by
      have hz : ∀ i, raw4544step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw4544step1 = (fun i j => raw4544step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4544step0 permutation57 hz
    injectiveMoment H raw4544step1 = injectiveMoment H raw4544step2 := by
      have heq : raw4544step2 = (fun i j => raw4544step1 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4544step1 permutation25 permutation19
    _ = injectiveMoment H node1244 := by rfl

def raw4545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 0, -1, 2], ![2, 0, 0, -2]]

def raw4545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![-1, -1, 2], ![2, 0, -2]]

def raw4545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical4545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4545 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw4545 = injectiveMoment H raw4545step0 := by
      have heq : raw4545step0 = raw4545.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4545).symm
    injectiveMoment H raw4545step0 = injectiveMoment H raw4545step1 := by
      have hz : ∀ i, raw4545step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw4545step1 = (fun i j => raw4545step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4545step0 permutation15 hz
    injectiveMoment H raw4545step1 = injectiveMoment H raw4545step2 := by
      have heq : raw4545step2 = (fun i j => raw4545step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4545step1 permutation22 permutation5
    _ = injectiveMoment H node279 := by rfl

def raw4546 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4546step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-1, 0, 0, 2, -1], ![2, 0, -1, -1, 0]]

def raw4546step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 0, 2, -1], ![2, -1, -1, 0]]

def raw4546step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

theorem canonical4546 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4546 = injectiveMoment H node1247 := by
  calc
    injectiveMoment H raw4546 = injectiveMoment H raw4546step0 := by
      have heq : raw4546step0 = raw4546.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4546).symm
    injectiveMoment H raw4546step0 = injectiveMoment H raw4546step1 := by
      have hz : ∀ i, raw4546step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw4546step1 = (fun i j => raw4546step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4546step0 permutation57 hz
    injectiveMoment H raw4546step1 = injectiveMoment H raw4546step2 := by
      have heq : raw4546step2 = (fun i j => raw4546step1 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4546step1 permutation31 permutation20
    _ = injectiveMoment H node1247 := by rfl

def raw4547 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4547step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-1, 0, 1, 1, -1], ![2, 0, -2, 0, 0]]

def raw4547step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 0, -1, 2, 0], ![1, 0, -1, -1, 1], ![-2, 0, 2, 0, 0]]

def raw4547step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, -1, -1, 1], ![-2, 2, 0, 0]]

def raw4547step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical4547 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4547 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw4547 = injectiveMoment H raw4547step0 := by
      have heq : raw4547step0 = raw4547.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4547).symm
    injectiveMoment H raw4547step0 = injectiveMoment H raw4547step1 := by
      have heq : raw4547step1 = -raw4547step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4547step0).symm
    injectiveMoment H raw4547step1 = injectiveMoment H raw4547step2 := by
      have hz : ∀ i, raw4547step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw4547step2 = (fun i j => raw4547step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4547step1 permutation57 hz
    injectiveMoment H raw4547step2 = injectiveMoment H raw4547step3 := by
      have heq : raw4547step3 = (fun i j => raw4547step2 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4547step2 permutation13 permutation32
    _ = injectiveMoment H node1058 := by rfl

def raw4548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw4548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 0, 2, -1], ![2, 0, -1, -1]]

def raw4548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![2, -1, -1]]

def raw4548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4548 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4548 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw4548 = injectiveMoment H raw4548step0 := by
      have heq : raw4548step0 = raw4548.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4548).symm
    injectiveMoment H raw4548step0 = injectiveMoment H raw4548step1 := by
      have hz : ∀ i, raw4548step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw4548step1 = (fun i j => raw4548step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4548step0 permutation15 hz
    injectiveMoment H raw4548step1 = injectiveMoment H raw4548step2 := by
      have heq : raw4548step2 = (fun i j => raw4548step1 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4548step1 permutation25 permutation7
    _ = injectiveMoment H node276 := by rfl

def raw4549 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4549step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, 1, 0, -1, 1], ![2, -1, 0, 0, -1]]

def raw4549step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -1, 1], ![2, -1, 0, -1]]

def raw4549step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

theorem canonical4549 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4549 = injectiveMoment H node1263 := by
  calc
    injectiveMoment H raw4549 = injectiveMoment H raw4549step0 := by
      have heq : raw4549step0 = raw4549.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4549).symm
    injectiveMoment H raw4549step0 = injectiveMoment H raw4549step1 := by
      have hz : ∀ i, raw4549step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw4549step1 = (fun i j => raw4549step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4549step0 permutation80 hz
    injectiveMoment H raw4549step1 = injectiveMoment H raw4549step2 := by
      have heq : raw4549step2 = (fun i j => raw4549step1 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4549step1 permutation27 permutation18
    _ = injectiveMoment H node1263 := by rfl

def raw4550 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1]]

theorem canonical4550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4550 = injectiveMoment H node2232 := by
  rfl

def raw4551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4551step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical4551 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4551 = injectiveMoment H node1749 := by
  calc
    injectiveMoment H raw4551 = injectiveMoment H raw4551step0 := by
      have heq : raw4551step0 = (fun i j => raw4551 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4551 permutation45 permutation11
    _ = injectiveMoment H node1749 := by rfl

def raw4552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4552step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem canonical4552 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4552 = injectiveMoment H node1791 := by
  calc
    injectiveMoment H raw4552 = injectiveMoment H raw4552step0 := by
      have heq : raw4552step0 = (fun i j => raw4552 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4552 permutation45 permutation11
    _ = injectiveMoment H node1791 := by rfl

def raw4553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

theorem canonical4553 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4553 = injectiveMoment H node2233 := by
  rfl

def raw4554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 0, 0]]

theorem canonical4554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4554 = injectiveMoment H node2234 := by
  rfl

def raw4555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -1, 1]]

theorem canonical4555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4555 = injectiveMoment H node2235 := by
  rfl

def raw4556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

theorem canonical4556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4556 = injectiveMoment H node2236 := by
  rfl

def raw4557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical4557 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4557 = injectiveMoment H node2227 := by
  calc
    injectiveMoment H raw4557 = injectiveMoment H raw4557step0 := by
      have heq : raw4557step0 = (fun i j => raw4557 (permutation114 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4557 permutation114 permutation16
    _ = injectiveMoment H node2227 := by rfl

def raw4558 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical4558 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4558 = injectiveMoment H node2237 := by
  rfl

def raw4559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical4559 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4559 = injectiveMoment H node2238 := by
  rfl

def raw4560 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw4560step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -2, 2], ![2, -1, 1, -2]]

def raw4560step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2]]

theorem canonical4560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4560 = injectiveMoment H node1370 := by
  calc
    injectiveMoment H raw4560 = injectiveMoment H raw4560step0 := by
      have heq : raw4560step0 = raw4560.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4560).symm
    injectiveMoment H raw4560step0 = injectiveMoment H raw4560step1 := by
      have heq : raw4560step1 = (fun i j => raw4560step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4560step0 permutation27 permutation17
    _ = injectiveMoment H node1370 := by rfl

def raw4561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4561step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical4561 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4561 = injectiveMoment H node1751 := by
  calc
    injectiveMoment H raw4561 = injectiveMoment H raw4561step0 := by
      have heq : raw4561step0 = (fun i j => raw4561 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4561 permutation40 permutation11
    _ = injectiveMoment H node1751 := by rfl

def raw4562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem canonical4562 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4562 = injectiveMoment H node1738 := by
  calc
    injectiveMoment H raw4562 = injectiveMoment H raw4562step0 := by
      have heq : raw4562step0 = (fun i j => raw4562 (permutation115 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4562 permutation115 permutation19
    _ = injectiveMoment H node1738 := by rfl

def raw4563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4563step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical4563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4563 = injectiveMoment H node1750 := by
  calc
    injectiveMoment H raw4563 = injectiveMoment H raw4563step0 := by
      have heq : raw4563step0 = (fun i j => raw4563 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4563 permutation39 permutation11
    _ = injectiveMoment H node1750 := by rfl

def raw4564 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4564step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -1, 1], ![2, -1, 0, -1]]

def raw4564step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

theorem canonical4564 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4564 = injectiveMoment H node1263 := by
  calc
    injectiveMoment H raw4564 = injectiveMoment H raw4564step0 := by
      have heq : raw4564step0 = raw4564.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4564).symm
    injectiveMoment H raw4564step0 = injectiveMoment H raw4564step1 := by
      have heq : raw4564step1 = (fun i j => raw4564step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4564step0 permutation27 permutation18
    _ = injectiveMoment H node1263 := by rfl

def raw4565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4565step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical4565 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4565 = injectiveMoment H node1793 := by
  calc
    injectiveMoment H raw4565 = injectiveMoment H raw4565step0 := by
      have heq : raw4565step0 = (fun i j => raw4565 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4565 permutation40 permutation11
    _ = injectiveMoment H node1793 := by rfl

def raw4566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw4566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical4566 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4566 = injectiveMoment H node2229 := by
  calc
    injectiveMoment H raw4566 = injectiveMoment H raw4566step0 := by
      have heq : raw4566step0 = (fun i j => raw4566 (permutation114 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4566 permutation114 permutation16
    _ = injectiveMoment H node2229 := by rfl

def raw4567 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4567step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical4567 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4567 = injectiveMoment H node1831 := by
  calc
    injectiveMoment H raw4567 = injectiveMoment H raw4567step0 := by
      have heq : raw4567step0 = (fun i j => raw4567 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4567 permutation34 permutation11
    _ = injectiveMoment H node1831 := by rfl

def raw4568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

theorem canonical4568 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4568 = injectiveMoment H node2239 := by
  rfl

def raw4569 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw4569step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, 1, -1], ![2, -1, -2, 1]]

def raw4569step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical4569 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4569 = injectiveMoment H node842 := by
  calc
    injectiveMoment H raw4569 = injectiveMoment H raw4569step0 := by
      have heq : raw4569step0 = raw4569.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4569).symm
    injectiveMoment H raw4569step0 = injectiveMoment H raw4569step1 := by
      have heq : raw4569step1 = (fun i j => raw4569step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4569step0 permutation27 permutation18
    _ = injectiveMoment H node842 := by rfl

def raw4570 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw4570step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, 2, -2], ![2, -1, -3, 2]]

def raw4570step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 2, -1, -2]]

theorem canonical4570 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4570 = injectiveMoment H node728 := by
  calc
    injectiveMoment H raw4570 = injectiveMoment H raw4570step0 := by
      have heq : raw4570step0 = raw4570.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4570).symm
    injectiveMoment H raw4570step0 = injectiveMoment H raw4570step1 := by
      have heq : raw4570step1 = (fun i j => raw4570step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4570step0 permutation27 permutation17
    _ = injectiveMoment H node728 := by rfl

def raw4571 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4571step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 1, 1, -1], ![2, -1, 0, -1]]

def raw4571step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical4571 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4571 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw4571 = injectiveMoment H raw4571step0 := by
      have heq : raw4571step0 = raw4571.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4571).symm
    injectiveMoment H raw4571step0 = injectiveMoment H raw4571step1 := by
      have heq : raw4571step1 = (fun i j => raw4571step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4571step0 permutation29 permutation20
    _ = injectiveMoment H node1078 := by rfl

def raw4572 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw4572step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 1, 2, -2], ![2, -1, -1, 0]]

def raw4572step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical4572 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4572 = injectiveMoment H node1276 := by
  calc
    injectiveMoment H raw4572 = injectiveMoment H raw4572step0 := by
      have heq : raw4572step0 = raw4572.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4572).symm
    injectiveMoment H raw4572step0 = injectiveMoment H raw4572step1 := by
      have heq : raw4572step1 = (fun i j => raw4572step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4572step0 permutation29 permutation20
    _ = injectiveMoment H node1276 := by rfl

def raw4573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4573step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

theorem canonical4573 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4573 = injectiveMoment H node2236 := by
  calc
    injectiveMoment H raw4573 = injectiveMoment H raw4573step0 := by
      have heq : raw4573step0 = (fun i j => raw4573 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4573 permutation39 permutation9
    _ = injectiveMoment H node2236 := by rfl

def raw4574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical4574 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4574 = injectiveMoment H node2240 := by
  rfl

def raw4575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw4575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical4575 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4575 = injectiveMoment H node2240 := by
  calc
    injectiveMoment H raw4575 = injectiveMoment H raw4575step0 := by
      have heq : raw4575step0 = (fun i j => raw4575 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4575 permutation34 permutation9
    _ = injectiveMoment H node2240 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
