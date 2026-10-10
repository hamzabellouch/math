import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8864 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, -3, 3]]

def raw8864step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![0, -1, -2, 3]]

def raw8864step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![0, 1, 2, -3]]

def raw8864step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical8864 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8864 = injectiveMoment H node968 := by
  calc
    injectiveMoment H raw8864 = injectiveMoment H raw8864step0 := by
      have heq : raw8864step0 = raw8864.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8864).symm
    injectiveMoment H raw8864step0 = injectiveMoment H raw8864step1 := by
      have heq : raw8864step1 = -raw8864step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8864step0).symm
    injectiveMoment H raw8864step1 = injectiveMoment H raw8864step2 := by
      have heq : raw8864step2 = (fun i j => raw8864step1 (permutation21 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8864step1 permutation21 permutation15
    _ = injectiveMoment H node968 := by rfl

def raw8865 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw8865step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical8865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8865 = injectiveMoment H node3044 := by
  calc
    injectiveMoment H raw8865 = injectiveMoment H raw8865step0 := by
      have heq : raw8865step0 = (fun i j => raw8865 (permutation355 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8865 permutation355 permutation11
    _ = injectiveMoment H node3044 := by rfl

def raw8866 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -1, -2, 2]]

def raw8866step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![-1, 1, 2, -2]]

def raw8866step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical8866 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8866 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw8866 = injectiveMoment H raw8866step0 := by
      have heq : raw8866step0 = -raw8866 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8866).symm
    injectiveMoment H raw8866step0 = injectiveMoment H raw8866step1 := by
      have heq : raw8866step1 = (fun i j => raw8866step0 (permutation130 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8866step0 permutation130 permutation13
    _ = injectiveMoment H node2449 := by rfl

def raw8867 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -2, 3]]

def raw8867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3]]

def raw8867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8867 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw8867 = injectiveMoment H raw8867step0 := by
      have hz : ∀ i, raw8867 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8867step0 = (fun i j => raw8867 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8867 permutation9 hz
    injectiveMoment H raw8867step0 = injectiveMoment H raw8867step1 := by
      have heq : raw8867step1 = (fun i j => raw8867step0 (permutation143 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8867step0 permutation143 permutation5
    _ = injectiveMoment H node570 := by rfl

def raw8868 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8868step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![-1, -2, 3]]

def raw8868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8868 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8868 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw8868 = injectiveMoment H raw8868step0 := by
      have hz : ∀ i, raw8868 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8868step0 = (fun i j => raw8868 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8868 permutation9 hz
    injectiveMoment H raw8868step0 = injectiveMoment H raw8868step1 := by
      have heq : raw8868step1 = (fun i j => raw8868step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8868step0 permutation31 permutation5
    _ = injectiveMoment H node185 := by rfl

def raw8869 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, -1, -3, 4]]

def raw8869step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -2, -1, 3], ![0, 1, 3, -4]]

def raw8869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -1, 1], ![-2, -1, 3], ![1, 3, -4]]

def raw8869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8869 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8869 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw8869 = injectiveMoment H raw8869step0 := by
      have heq : raw8869step0 = -raw8869 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8869).symm
    injectiveMoment H raw8869step0 = injectiveMoment H raw8869step1 := by
      have hz : ∀ i, raw8869step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8869step1 = (fun i j => raw8869step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8869step0 permutation9 hz
    injectiveMoment H raw8869step1 = injectiveMoment H raw8869step2 := by
      have heq : raw8869step2 = (fun i j => raw8869step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8869step1 permutation23 permutation3
    _ = injectiveMoment H node173 := by rfl

def raw8870 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -1, -3, 3]]

def raw8870step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, 2, 0, -3], ![0, -2, -1, 3]]

def raw8870step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, -2, 0, 3], ![0, 2, 1, -3]]

def raw8870step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical8870 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8870 = injectiveMoment H node803 := by
  calc
    injectiveMoment H raw8870 = injectiveMoment H raw8870step0 := by
      have heq : raw8870step0 = raw8870.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8870).symm
    injectiveMoment H raw8870step0 = injectiveMoment H raw8870step1 := by
      have heq : raw8870step1 = -raw8870step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8870step0).symm
    injectiveMoment H raw8870step1 = injectiveMoment H raw8870step2 := by
      have heq : raw8870step2 = (fun i j => raw8870step1 (permutation22 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8870step1 permutation22 permutation9
    _ = injectiveMoment H node803 := by rfl

def raw8871 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -1, -3, 4]]

def raw8871step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -2, 2], ![0, -2, 0, 2], ![0, 1, 3, -4]]

def raw8871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![-2, 0, 2], ![1, 3, -4]]

def raw8871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8871 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8871 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw8871 = injectiveMoment H raw8871step0 := by
      have heq : raw8871step0 = -raw8871 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8871).symm
    injectiveMoment H raw8871step0 = injectiveMoment H raw8871step1 := by
      have hz : ∀ i, raw8871step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8871step1 = (fun i j => raw8871step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8871step0 permutation9 hz
    injectiveMoment H raw8871step1 = injectiveMoment H raw8871step2 := by
      have heq : raw8871step2 = (fun i j => raw8871step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8871step1 permutation23 permutation3
    _ = injectiveMoment H node201 := by rfl

def raw8872 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![-1, 1, 1, -1], ![1, -1, 1, -1]]

def raw8872step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![1, -3, 1, 1], ![0, 2, -1, -1]]

def raw8872step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![-1, 3, -1, -1], ![0, -2, 1, 1]]

def raw8872step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical8872 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8872 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw8872 = injectiveMoment H raw8872step0 := by
      have heq : raw8872step0 = raw8872.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8872).symm
    injectiveMoment H raw8872step0 = injectiveMoment H raw8872step1 := by
      have heq : raw8872step1 = -raw8872step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8872step0).symm
    injectiveMoment H raw8872step1 = injectiveMoment H raw8872step2 := by
      have heq : raw8872step2 = (fun i j => raw8872step1 (permutation22 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8872step1 permutation22 permutation14
    _ = injectiveMoment H node936 := by rfl

def raw8873 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw8873step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![1, -3, 2, 0], ![0, 2, -2, 0]]

def raw8873step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical8873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8873 = injectiveMoment H node1109 := by
  calc
    injectiveMoment H raw8873 = injectiveMoment H raw8873step0 := by
      have heq : raw8873step0 = raw8873.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8873).symm
    injectiveMoment H raw8873step0 = injectiveMoment H raw8873step1 := by
      have heq : raw8873step1 = (fun i j => raw8873step0 (permutation19 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8873step0 permutation19 permutation14
    _ = injectiveMoment H node1109 := by rfl

def raw8874 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![0, -1, 1, 0]]

def raw8874step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, -1, 3, -2], ![0, -1, -1, 2], ![0, 1, -1, 0]]

def raw8874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0]]

def raw8874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8874 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8874 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw8874 = injectiveMoment H raw8874step0 := by
      have heq : raw8874step0 = -raw8874 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8874).symm
    injectiveMoment H raw8874step0 = injectiveMoment H raw8874step1 := by
      have hz : ∀ i, raw8874step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8874step1 = (fun i j => raw8874step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8874step0 permutation9 hz
    injectiveMoment H raw8874step1 = injectiveMoment H raw8874step2 := by
      have heq : raw8874step2 = (fun i j => raw8874step1 (permutation16 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8874step1 permutation16 permutation7
    _ = injectiveMoment H node176 := by rfl

def raw8875 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![0, -1, 0, 1]]

def raw8875step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, -1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1]]

def raw8875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 3, -2], ![-1, -2, 3], ![1, 0, -1]]

def raw8875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8875 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8875 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw8875 = injectiveMoment H raw8875step0 := by
      have heq : raw8875step0 = -raw8875 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8875).symm
    injectiveMoment H raw8875step0 = injectiveMoment H raw8875step1 := by
      have hz : ∀ i, raw8875step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8875step1 = (fun i j => raw8875step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8875step0 permutation9 hz
    injectiveMoment H raw8875step1 = injectiveMoment H raw8875step2 := by
      have heq : raw8875step2 = (fun i j => raw8875step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8875step1 permutation23 permutation3
    _ = injectiveMoment H node263 := by rfl

def raw8876 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -2, 1], ![-1, 1, 2, -2], ![1, -1, -1, 1]]

def raw8876step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical8876 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8876 = injectiveMoment H node835 := by
  calc
    injectiveMoment H raw8876 = injectiveMoment H raw8876step0 := by
      have heq : raw8876step0 = (fun i j => raw8876 (permutation21 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8876 permutation21 permutation13
    _ = injectiveMoment H node835 := by rfl

def raw8877 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![0, -1, -1, 2]]

def raw8877step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, -1, 2, -1], ![0, -1, -2, 3], ![0, 1, 1, -2]]

def raw8877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 2, -1], ![-1, -2, 3], ![1, 1, -2]]

def raw8877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8877 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8877 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw8877 = injectiveMoment H raw8877step0 := by
      have heq : raw8877step0 = -raw8877 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8877).symm
    injectiveMoment H raw8877step0 = injectiveMoment H raw8877step1 := by
      have hz : ∀ i, raw8877step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8877step1 = (fun i j => raw8877step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8877step0 permutation9 hz
    injectiveMoment H raw8877step1 = injectiveMoment H raw8877step2 := by
      have heq : raw8877step2 = (fun i j => raw8877step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8877step1 permutation23 permutation3
    _ = injectiveMoment H node261 := by rfl

def raw8878 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw8878step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical8878 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8878 = injectiveMoment H node3044 := by
  calc
    injectiveMoment H raw8878 = injectiveMoment H raw8878step0 := by
      have heq : raw8878step0 = (fun i j => raw8878 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8878 permutation308 permutation9
    _ = injectiveMoment H node3044 := by rfl

def raw8879 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, -1, 1]]

def raw8879step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![1, 0, -1], ![0, -1, 1]]

def raw8879step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8879 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8879 = injectiveMoment H node64 := by
  calc
    injectiveMoment H raw8879 = injectiveMoment H raw8879step0 := by
      have hz : ∀ i, raw8879 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8879step0 = (fun i j => raw8879 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8879 permutation9 hz
    injectiveMoment H raw8879step0 = injectiveMoment H raw8879step1 := by
      have heq : raw8879step1 = (fun i j => raw8879step0 (permutation4 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8879step0 permutation4 permutation4
    _ = injectiveMoment H node64 := by rfl

def raw8880 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![1, -2, 2, -1], ![-1, 3, -3, 1]]

def raw8880step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![1, 2, -3], ![0, -1, 1]]

def raw8880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical8880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8880 = injectiveMoment H node267 := by
  calc
    injectiveMoment H raw8880 = injectiveMoment H raw8880step0 := by
      have heq : raw8880step0 = raw8880.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8880).symm
    injectiveMoment H raw8880step0 = injectiveMoment H raw8880step1 := by
      have heq : raw8880step1 = (fun i j => raw8880step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8880step0 permutation19 permutation3
    _ = injectiveMoment H node267 := by rfl

def raw8881 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![1, -1, 1, -1], ![-1, 2, -2, 1]]

def raw8881step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![1, 1, -2], ![0, -1, 1]]

def raw8881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical8881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8881 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw8881 = injectiveMoment H raw8881step0 := by
      have heq : raw8881step0 = raw8881.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8881).symm
    injectiveMoment H raw8881step0 = injectiveMoment H raw8881step1 := by
      have heq : raw8881step1 = (fun i j => raw8881step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8881step0 permutation19 permutation3
    _ = injectiveMoment H node283 := by rfl

def raw8882 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![1, -1, 2, -2], ![-1, 2, -3, 2]]

def raw8882step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![1, 2, -3], ![0, -2, 2]]

def raw8882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![-1, -2, 3], ![0, 2, -2]]

def raw8882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8882 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8882 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw8882 = injectiveMoment H raw8882step0 := by
      have heq : raw8882step0 = raw8882.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8882).symm
    injectiveMoment H raw8882step0 = injectiveMoment H raw8882step1 := by
      have heq : raw8882step1 = -raw8882step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8882step0).symm
    injectiveMoment H raw8882step1 = injectiveMoment H raw8882step2 := by
      have heq : raw8882step2 = (fun i j => raw8882step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8882step1 permutation22 permutation3
    _ = injectiveMoment H node268 := by rfl

def raw8883 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![2, -1, 1, -2], ![-2, 2, -2, 2]]

def raw8883step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -1, 2], ![1, 1, -2], ![0, -2, 2]]

def raw8883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8883 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8883 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw8883 = injectiveMoment H raw8883step0 := by
      have heq : raw8883step0 = raw8883.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8883).symm
    injectiveMoment H raw8883step0 = injectiveMoment H raw8883step1 := by
      have heq : raw8883step1 = (fun i j => raw8883step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8883step0 permutation19 permutation3
    _ = injectiveMoment H node279 := by rfl

def raw8884 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-4, 2, -1, 3], ![4, -1, -1, -2]]

def raw8884step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![2, -1, -1], ![-1, 3, -2]]

def raw8884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-2, 1, 1], ![1, -3, 2]]

def raw8884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

theorem canonical8884 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8884 = injectiveMoment H node219 := by
  calc
    injectiveMoment H raw8884 = injectiveMoment H raw8884step0 := by
      have heq : raw8884step0 = raw8884.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8884).symm
    injectiveMoment H raw8884step0 = injectiveMoment H raw8884step1 := by
      have heq : raw8884step1 = -raw8884step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8884step0).symm
    injectiveMoment H raw8884step1 = injectiveMoment H raw8884step2 := by
      have heq : raw8884step2 = (fun i j => raw8884step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8884step1 permutation21 permutation4
    _ = injectiveMoment H node219 := by rfl

def raw8885 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-4, 2, 0, 2], ![4, -1, -2, -1]]

def raw8885step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![2, 0, -2], ![-1, 2, -1]]

def raw8885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-2, 0, 2], ![1, -2, 1]]

def raw8885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical8885 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8885 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw8885 = injectiveMoment H raw8885step0 := by
      have heq : raw8885step0 = raw8885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8885).symm
    injectiveMoment H raw8885step0 = injectiveMoment H raw8885step1 := by
      have heq : raw8885step1 = -raw8885step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8885step0).symm
    injectiveMoment H raw8885step1 = injectiveMoment H raw8885step2 := by
      have heq : raw8885step2 = (fun i j => raw8885step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8885step1 permutation21 permutation3
    _ = injectiveMoment H node218 := by rfl

def raw8886 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, -1, 0, 4], ![3, 2, -2, -3]]

def raw8886step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![2, 0, -2], ![-1, 4, -3]]

def raw8886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![-2, 0, 2], ![1, -4, 3]]

def raw8886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

theorem canonical8886 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8886 = injectiveMoment H node213 := by
  calc
    injectiveMoment H raw8886 = injectiveMoment H raw8886step0 := by
      have heq : raw8886step0 = raw8886.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8886).symm
    injectiveMoment H raw8886step0 = injectiveMoment H raw8886step1 := by
      have heq : raw8886step1 = -raw8886step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8886step0).symm
    injectiveMoment H raw8886step1 = injectiveMoment H raw8886step2 := by
      have heq : raw8886step2 = (fun i j => raw8886step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8886step1 permutation22 permutation3
    _ = injectiveMoment H node213 := by rfl

def raw8887 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 2, -1, 2], ![3, -1, -1, -1]]

def raw8887step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![2, -1, -1], ![-1, 2, -1]]

def raw8887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-2, 1, 1], ![1, -2, 1]]

def raw8887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical8887 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8887 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw8887 = injectiveMoment H raw8887step0 := by
      have heq : raw8887step0 = raw8887.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8887).symm
    injectiveMoment H raw8887step0 = injectiveMoment H raw8887step1 := by
      have heq : raw8887step1 = -raw8887step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8887step0).symm
    injectiveMoment H raw8887step1 = injectiveMoment H raw8887step2 := by
      have heq : raw8887step2 = (fun i j => raw8887step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8887step1 permutation21 permutation4
    _ = injectiveMoment H node223 := by rfl

def raw8888 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 2, 0, 1], ![3, -1, -2, 0]]

def raw8888step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![2, 0, -2], ![-1, 1, 0]]

def raw8888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-2, 0, 2], ![1, -1, 0]]

def raw8888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical8888 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8888 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw8888 = injectiveMoment H raw8888step0 := by
      have heq : raw8888step0 = raw8888.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8888).symm
    injectiveMoment H raw8888step0 = injectiveMoment H raw8888step1 := by
      have heq : raw8888step1 = -raw8888step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8888step0).symm
    injectiveMoment H raw8888step1 = injectiveMoment H raw8888step2 := by
      have heq : raw8888step2 = (fun i j => raw8888step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8888step1 permutation21 permutation3
    _ = injectiveMoment H node215 := by rfl

def raw8889 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 2, 1, 0], ![3, -1, -3, 1]]

def raw8889step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![2, 1, -3], ![-1, 0, 1]]

def raw8889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-2, -1, 3], ![1, 0, -1]]

def raw8889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8889 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw8889 = injectiveMoment H raw8889step0 := by
      have heq : raw8889step0 = raw8889.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8889).symm
    injectiveMoment H raw8889step0 = injectiveMoment H raw8889step1 := by
      have heq : raw8889step1 = -raw8889step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8889step0).symm
    injectiveMoment H raw8889step1 = injectiveMoment H raw8889step2 := by
      have heq : raw8889step2 = (fun i j => raw8889step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8889step1 permutation21 permutation3
    _ = injectiveMoment H node187 := by rfl

def raw8890 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 3, 0, 0], ![3, -2, -2, 1]]

def raw8890step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1]]

def raw8890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -3, 2], ![-2, 0, 2], ![1, 0, -1]]

def raw8890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical8890 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8890 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw8890 = injectiveMoment H raw8890step0 := by
      have heq : raw8890step0 = raw8890.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8890).symm
    injectiveMoment H raw8890step0 = injectiveMoment H raw8890step1 := by
      have heq : raw8890step1 = -raw8890step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8890step0).symm
    injectiveMoment H raw8890step1 = injectiveMoment H raw8890step2 := by
      have heq : raw8890step2 = (fun i j => raw8890step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8890step1 permutation21 permutation3
    _ = injectiveMoment H node214 := by rfl

def raw8891 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -2, 2, 2], ![2, 3, -4, -1]]

def raw8891step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -2, 3], ![2, 2, -4], ![-1, 2, -1]]

def raw8891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 2, -3], ![-2, -2, 4], ![1, -2, 1]]

def raw8891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

theorem canonical8891 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8891 = injectiveMoment H node152 := by
  calc
    injectiveMoment H raw8891 = injectiveMoment H raw8891step0 := by
      have heq : raw8891step0 = raw8891.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8891).symm
    injectiveMoment H raw8891step0 = injectiveMoment H raw8891step1 := by
      have heq : raw8891step1 = -raw8891step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8891step0).symm
    injectiveMoment H raw8891step1 = injectiveMoment H raw8891step2 := by
      have heq : raw8891step2 = (fun i j => raw8891step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8891step1 permutation22 permutation3
    _ = injectiveMoment H node152 := by rfl

def raw8892 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, -2, 5], ![2, 2, 0, -4]]

def raw8892step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, -2, 0], ![-1, 5, -4]]

def raw8892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 2, 0], ![1, -5, 4]]

def raw8892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

theorem canonical8892 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8892 = injectiveMoment H node200 := by
  calc
    injectiveMoment H raw8892 = injectiveMoment H raw8892step0 := by
      have heq : raw8892step0 = raw8892.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8892).symm
    injectiveMoment H raw8892step0 = injectiveMoment H raw8892step1 := by
      have heq : raw8892step1 = -raw8892step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8892step0).symm
    injectiveMoment H raw8892step1 = injectiveMoment H raw8892step2 := by
      have heq : raw8892step2 = (fun i j => raw8892step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8892step1 permutation21 permutation4
    _ = injectiveMoment H node200 := by rfl

def raw8893 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, -1, 4], ![2, 2, -1, -3]]

def raw8893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, -1, -1], ![-1, 4, -3]]

def raw8893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 1, 1], ![1, -4, 3]]

def raw8893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8893 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8893 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw8893 = injectiveMoment H raw8893step0 := by
      have heq : raw8893step0 = raw8893.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8893).symm
    injectiveMoment H raw8893step0 = injectiveMoment H raw8893step1 := by
      have heq : raw8893step1 = -raw8893step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8893step0).symm
    injectiveMoment H raw8893step1 = injectiveMoment H raw8893step2 := by
      have heq : raw8893step2 = (fun i j => raw8893step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8893step1 permutation21 permutation4
    _ = injectiveMoment H node225 := by rfl

def raw8894 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, 0, 3], ![2, 2, -2, -2]]

def raw8894step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, 0, -2], ![-1, 3, -2]]

def raw8894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 0, 2], ![1, -3, 2]]

def raw8894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical8894 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8894 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw8894 = injectiveMoment H raw8894step0 := by
      have heq : raw8894step0 = raw8894.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8894).symm
    injectiveMoment H raw8894step0 = injectiveMoment H raw8894step1 := by
      have heq : raw8894step1 = -raw8894step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8894step0).symm
    injectiveMoment H raw8894step1 = injectiveMoment H raw8894step2 := by
      have heq : raw8894step2 = (fun i j => raw8894step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8894step1 permutation22 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw8895 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, 3, 0], ![2, 2, -5, 1]]

def raw8895step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, 3, -5], ![-1, 0, 1]]

def raw8895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, -3, 5], ![1, 0, -1]]

def raw8895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8895 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8895 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw8895 = injectiveMoment H raw8895step0 := by
      have heq : raw8895step0 = raw8895.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8895).symm
    injectiveMoment H raw8895step0 = injectiveMoment H raw8895step1 := by
      have heq : raw8895step1 = -raw8895step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8895step0).symm
    injectiveMoment H raw8895step1 = injectiveMoment H raw8895step2 := by
      have heq : raw8895step2 = (fun i j => raw8895step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8895step1 permutation22 permutation3
    _ = injectiveMoment H node127 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
