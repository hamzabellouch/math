import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 2, -3], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1024step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![-1, 2, -1, 0], ![5, -3, -1, -1]]

def raw1024step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1024 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1024 = injectiveMoment H node886 := by
  calc
    injectiveMoment H raw1024 = injectiveMoment H raw1024step0 := by
      have heq : raw1024step0 = raw1024.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1024).symm
    injectiveMoment H raw1024step0 = injectiveMoment H raw1024step1 := by
      have heq : raw1024step1 = (fun i j => raw1024step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1024step0 permutation32 permutation32
    _ = injectiveMoment H node886 := by rfl

def raw1025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1025step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![-1, -1, 0, 2], ![5, -1, -1, -3]]

def raw1025step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1025 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1025 = injectiveMoment H node887 := by
  calc
    injectiveMoment H raw1025 = injectiveMoment H raw1025step0 := by
      have heq : raw1025step0 = raw1025.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1025).symm
    injectiveMoment H raw1025step0 = injectiveMoment H raw1025step1 := by
      have heq : raw1025step1 = (fun i j => raw1025step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1025step0 permutation32 permutation24
    _ = injectiveMoment H node887 := by rfl

def raw1026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, -1, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw1026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![-1, -1, 1, 1], ![5, -1, -2, -2]]

def raw1026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical1026 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1026 = injectiveMoment H node392 := by
  calc
    injectiveMoment H raw1026 = injectiveMoment H raw1026step0 := by
      have heq : raw1026step0 = raw1026.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1026).symm
    injectiveMoment H raw1026step0 = injectiveMoment H raw1026step1 := by
      have heq : raw1026step1 = (fun i j => raw1026step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1026step0 permutation30 permutation26
    _ = injectiveMoment H node392 := by rfl

def raw1027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1027step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![-1, 0, -1, 2], ![5, -2, 0, -3]]

def raw1027step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![1, 0, 1, -2], ![-5, 2, 0, 3]]

def raw1027step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 2, 3, -5], ![1, 0, -2, 1]]

theorem canonical1027 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1027 = injectiveMoment H node1233 := by
  calc
    injectiveMoment H raw1027 = injectiveMoment H raw1027step0 := by
      have heq : raw1027step0 = raw1027.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1027).symm
    injectiveMoment H raw1027step0 = injectiveMoment H raw1027step1 := by
      have heq : raw1027step1 = -raw1027step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1027step0).symm
    injectiveMoment H raw1027step1 = injectiveMoment H raw1027step2 := by
      have heq : raw1027step2 = (fun i j => raw1027step1 (permutation10 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1027step1 permutation10 permutation24
    _ = injectiveMoment H node1233 := by rfl

def raw1028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, 0, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1028 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1028 = injectiveMoment H node751 := by
  calc
    injectiveMoment H raw1028 = injectiveMoment H raw1028step0 := by
      have heq : raw1028step0 = (fun i j => raw1028 (permutation11 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1028 permutation11 permutation23
    _ = injectiveMoment H node751 := by rfl

def raw1029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, 1, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![-1, 1, 0, 0], ![5, -3, -1, -1]]

def raw1029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical1029 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1029 = injectiveMoment H node888 := by
  calc
    injectiveMoment H raw1029 = injectiveMoment H raw1029step0 := by
      have heq : raw1029step0 = raw1029.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1029).symm
    injectiveMoment H raw1029step0 = injectiveMoment H raw1029step1 := by
      have heq : raw1029step1 = (fun i j => raw1029step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1029step0 permutation32 permutation26
    _ = injectiveMoment H node888 := by rfl

def raw1030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical1030 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1030 = injectiveMoment H node2736 := by
  calc
    injectiveMoment H raw1030 = injectiveMoment H raw1030step0 := by
      have heq : raw1030step0 = (fun i j => raw1030 (permutation60 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1030 permutation60 permutation21
    _ = injectiveMoment H node2736 := by rfl

def raw1031 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical1031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1031 = injectiveMoment H node1454 := by
  rfl

def raw1032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem canonical1032 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1032 = injectiveMoment H node1455 := by
  rfl

def raw1033 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1033step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

theorem canonical1033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1033 = injectiveMoment H node1456 := by
  calc
    injectiveMoment H raw1033 = injectiveMoment H raw1033step0 := by
      have heq : raw1033step0 = (fun i j => raw1033 (permutation35 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1033 permutation35 permutation15
    _ = injectiveMoment H node1456 := by rfl

def raw1034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def raw1034step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-2, 0, -1, 3]]

def raw1034step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, 0, -1]]

theorem canonical1034 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1034 = injectiveMoment H node795 := by
  calc
    injectiveMoment H raw1034 = injectiveMoment H raw1034step0 := by
      have heq : raw1034step0 = -raw1034 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1034).symm
    injectiveMoment H raw1034step0 = injectiveMoment H raw1034step1 := by
      have heq : raw1034step1 = (fun i j => raw1034step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1034step0 permutation31 permutation21
    _ = injectiveMoment H node795 := by rfl

def raw1035 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1035step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 0, 1, 1], ![0, 0, 1, -1, 0], ![4, 0, -1, 0, -3]]

def raw1035step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![4, -1, 0, -3]]

def raw1035step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical1035 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1035 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw1035 = injectiveMoment H raw1035step0 := by
      have heq : raw1035step0 = raw1035.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1035).symm
    injectiveMoment H raw1035step0 = injectiveMoment H raw1035step1 := by
      have hz : ∀ i, raw1035step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1035step1 = (fun i j => raw1035step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1035step0 permutation57 hz
    injectiveMoment H raw1035step1 = injectiveMoment H raw1035step2 := by
      have heq : raw1035step2 = (fun i j => raw1035step1 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1035step1 permutation27 permutation18
    _ = injectiveMoment H node1178 := by rfl

def raw1036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 0, 1, -1], ![4, 0, -2, -2]]

def raw1036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![4, -2, -2]]

def raw1036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1036 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1036 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw1036 = injectiveMoment H raw1036step0 := by
      have heq : raw1036step0 = raw1036.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1036).symm
    injectiveMoment H raw1036step0 = injectiveMoment H raw1036step1 := by
      have hz : ∀ i, raw1036step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1036step1 = (fun i j => raw1036step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1036step0 permutation15 hz
    injectiveMoment H raw1036step1 = injectiveMoment H raw1036step2 := by
      have heq : raw1036step2 = (fun i j => raw1036step1 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1036step1 permutation28 permutation6
    _ = injectiveMoment H node153 := by rfl

def raw1037 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1037step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 0, 1, 1], ![0, 1, 0, -1, 0], ![4, -1, 0, 0, -3]]

def raw1037step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![4, -1, 0, -3]]

def raw1037step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical1037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1037 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw1037 = injectiveMoment H raw1037step0 := by
      have heq : raw1037step0 = raw1037.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1037).symm
    injectiveMoment H raw1037step0 = injectiveMoment H raw1037step1 := by
      have hz : ∀ i, raw1037step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw1037step1 = (fun i j => raw1037step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1037step0 permutation80 hz
    injectiveMoment H raw1037step1 = injectiveMoment H raw1037step2 := by
      have heq : raw1037step2 = (fun i j => raw1037step1 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1037step1 permutation27 permutation18
    _ = injectiveMoment H node1178 := by rfl

def raw1038 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem canonical1038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1038 = injectiveMoment H node1457 := by
  rfl

def raw1039 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem canonical1039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1039 = injectiveMoment H node1458 := by
  rfl

def raw1040 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical1040 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1040 = injectiveMoment H node1459 := by
  rfl

def raw1041 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical1041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1041 = injectiveMoment H node1460 := by
  rfl

def raw1042 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical1042 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1042 = injectiveMoment H node1461 := by
  rfl

def raw1043 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1043step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical1043 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1043 = injectiveMoment H node1460 := by
  calc
    injectiveMoment H raw1043 = injectiveMoment H raw1043step0 := by
      have heq : raw1043step0 = (fun i j => raw1043 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1043 permutation34 permutation15
    _ = injectiveMoment H node1460 := by rfl

def raw1044 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1044step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem canonical1044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1044 = injectiveMoment H node1458 := by
  calc
    injectiveMoment H raw1044 = injectiveMoment H raw1044step0 := by
      have heq : raw1044step0 = (fun i j => raw1044 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1044 permutation33 permutation15
    _ = injectiveMoment H node1458 := by rfl

def raw1045 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1045step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical1045 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1045 = injectiveMoment H node1459 := by
  calc
    injectiveMoment H raw1045 = injectiveMoment H raw1045step0 := by
      have heq : raw1045step0 = (fun i j => raw1045 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1045 permutation33 permutation15
    _ = injectiveMoment H node1459 := by rfl

def raw1046 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1046 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1046 = injectiveMoment H node1462 := by
  rfl

def raw1047 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

theorem canonical1047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1047 = injectiveMoment H node1463 := by
  rfl

def raw1048 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical1048 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1048 = injectiveMoment H node1464 := by
  rfl

def raw1049 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem canonical1049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1049 = injectiveMoment H node1465 := by
  rfl

def raw1050 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem canonical1050 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1050 = injectiveMoment H node1466 := by
  rfl

def raw1051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 1, -4]]

def raw1051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, -2, 1], ![4, -1, 1, -4]]

def raw1051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

theorem canonical1051 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1051 = injectiveMoment H node1325 := by
  calc
    injectiveMoment H raw1051 = injectiveMoment H raw1051step0 := by
      have heq : raw1051step0 = raw1051.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1051).symm
    injectiveMoment H raw1051step0 = injectiveMoment H raw1051step1 := by
      have heq : raw1051step1 = (fun i j => raw1051step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1051step0 permutation27 permutation18
    _ = injectiveMoment H node1325 := by rfl

def raw1052 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

theorem canonical1052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1052 = injectiveMoment H node1467 := by
  rfl

def raw1053 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1053step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2]]

def raw1053step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1053 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1053 = injectiveMoment H node2739 := by
  calc
    injectiveMoment H raw1053 = injectiveMoment H raw1053step0 := by
      have heq : raw1053step0 = -raw1053 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1053).symm
    injectiveMoment H raw1053step0 = injectiveMoment H raw1053step1 := by
      have heq : raw1053step1 = (fun i j => raw1053step0 (permutation78 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1053step0 permutation78 permutation21
    _ = injectiveMoment H node2739 := by rfl

def raw1054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1054 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1054 = injectiveMoment H node1468 := by
  rfl

def raw1055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical1055 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1055 = injectiveMoment H node1469 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
