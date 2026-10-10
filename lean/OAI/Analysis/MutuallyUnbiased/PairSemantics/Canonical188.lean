import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6016step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6016 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6016 = injectiveMoment H node899 := by
  calc
    injectiveMoment H raw6016 = injectiveMoment H raw6016step0 := by
      have heq : raw6016step0 = (fun i j => raw6016 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6016 permutation9 permutation15
    _ = injectiveMoment H node899 := by rfl

def raw6017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical6017 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6017 = injectiveMoment H node1553 := by
  calc
    injectiveMoment H raw6017 = injectiveMoment H raw6017step0 := by
      have heq : raw6017step0 = (fun i j => raw6017 (permutation33 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6017 permutation33 permutation21
    _ = injectiveMoment H node1553 := by rfl

def raw6018 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6018 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6018 = injectiveMoment H node2487 := by
  rfl

def raw6019 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical6019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6019 = injectiveMoment H node2489 := by
  rfl

def raw6020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw6020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6020 = injectiveMoment H node464 := by
  calc
    injectiveMoment H raw6020 = injectiveMoment H raw6020step0 := by
      have heq : raw6020step0 = (fun i j => raw6020 (permutation13 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6020 permutation13 permutation21
    _ = injectiveMoment H node464 := by rfl

def raw6021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

theorem canonical6021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6021 = injectiveMoment H node891 := by
  rfl

def raw6022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw6022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6022 = injectiveMoment H node766 := by
  calc
    injectiveMoment H raw6022 = injectiveMoment H raw6022step0 := by
      have heq : raw6022step0 = (fun i j => raw6022 (permutation12 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6022 permutation12 permutation17
    _ = injectiveMoment H node766 := by rfl

def raw6023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw6023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical6023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6023 = injectiveMoment H node922 := by
  calc
    injectiveMoment H raw6023 = injectiveMoment H raw6023step0 := by
      have heq : raw6023step0 = (fun i j => raw6023 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6023 permutation14 permutation15
    _ = injectiveMoment H node922 := by rfl

def raw6024 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6024step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem canonical6024 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6024 = injectiveMoment H node1548 := by
  calc
    injectiveMoment H raw6024 = injectiveMoment H raw6024step0 := by
      have heq : raw6024step0 = (fun i j => raw6024 (permutation50 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6024 permutation50 permutation23
    _ = injectiveMoment H node1548 := by rfl

def raw6025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 2, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6025step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

theorem canonical6025 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6025 = injectiveMoment H node891 := by
  calc
    injectiveMoment H raw6025 = injectiveMoment H raw6025step0 := by
      have heq : raw6025step0 = (fun i j => raw6025 (permutation11 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6025 permutation11 permutation15
    _ = injectiveMoment H node891 := by rfl

def raw6026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-2, 3, 0, -1], ![4, -3, 0, -1]]

def raw6026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![2, -3, 0, 1], ![-4, 3, 0, 1]]

def raw6026step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -4, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical6026 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6026 = injectiveMoment H node1121 := by
  calc
    injectiveMoment H raw6026 = injectiveMoment H raw6026step0 := by
      have heq : raw6026step0 = raw6026.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6026).symm
    injectiveMoment H raw6026step0 = injectiveMoment H raw6026step1 := by
      have heq : raw6026step1 = -raw6026step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6026step0).symm
    injectiveMoment H raw6026step1 = injectiveMoment H raw6026step2 := by
      have heq : raw6026step2 = (fun i j => raw6026step1 (permutation14 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6026step1 permutation14 permutation25
    _ = injectiveMoment H node1121 := by rfl

def raw6027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 2, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6027step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical6027 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6027 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw6027 = injectiveMoment H raw6027step0 := by
      have heq : raw6027step0 = (fun i j => raw6027 (permutation9 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6027 permutation9 permutation21
    _ = injectiveMoment H node454 := by rfl

def raw6028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 2, 1, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-2, 1, 2, -1], ![4, -2, -2, 0]]

def raw6028step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -2, 1, 0], ![2, -1, -2, 1], ![-4, 2, 2, 0]]

def raw6028step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

theorem canonical6028 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6028 = injectiveMoment H node1127 := by
  calc
    injectiveMoment H raw6028 = injectiveMoment H raw6028step0 := by
      have heq : raw6028step0 = raw6028.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6028).symm
    injectiveMoment H raw6028step0 = injectiveMoment H raw6028step1 := by
      have heq : raw6028step1 = -raw6028step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6028step0).symm
    injectiveMoment H raw6028step1 = injectiveMoment H raw6028step2 := by
      have heq : raw6028step2 = (fun i j => raw6028step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6028step1 permutation10 permutation32
    _ = injectiveMoment H node1127 := by rfl

def raw6029 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw6029step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical6029 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6029 = injectiveMoment H node1560 := by
  calc
    injectiveMoment H raw6029 = injectiveMoment H raw6029step0 := by
      have heq : raw6029step0 = (fun i j => raw6029 (permutation43 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6029 permutation43 permutation21
    _ = injectiveMoment H node1560 := by rfl

def raw6030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw6030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6030 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6030 = injectiveMoment H node2483 := by
  calc
    injectiveMoment H raw6030 = injectiveMoment H raw6030step0 := by
      have heq : raw6030step0 = (fun i j => raw6030 (permutation35 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6030 permutation35 permutation15
    _ = injectiveMoment H node2483 := by rfl

def raw6031 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6031step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6031 = injectiveMoment H node2402 := by
  calc
    injectiveMoment H raw6031 = injectiveMoment H raw6031step0 := by
      have heq : raw6031step0 = (fun i j => raw6031 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6031 permutation45 permutation11
    _ = injectiveMoment H node2402 := by rfl

def raw6032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw6032step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical6032 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6032 = injectiveMoment H node2493 := by
  calc
    injectiveMoment H raw6032 = injectiveMoment H raw6032step0 := by
      have heq : raw6032step0 = (fun i j => raw6032 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6032 permutation35 permutation9
    _ = injectiveMoment H node2493 := by rfl

def raw6033 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![0, 1, 1, -2]]

def raw6033step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical6033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6033 = injectiveMoment H node2495 := by
  calc
    injectiveMoment H raw6033 = injectiveMoment H raw6033step0 := by
      have heq : raw6033step0 = (fun i j => raw6033 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6033 permutation34 permutation9
    _ = injectiveMoment H node2495 := by rfl

def raw6034 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6034step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6034 = injectiveMoment H node2494 := by
  calc
    injectiveMoment H raw6034 = injectiveMoment H raw6034step0 := by
      have heq : raw6034step0 = (fun i j => raw6034 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6034 permutation35 permutation9
    _ = injectiveMoment H node2494 := by rfl

def raw6035 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 1, 0, -1]]

def raw6035step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical6035 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6035 = injectiveMoment H node2390 := by
  calc
    injectiveMoment H raw6035 = injectiveMoment H raw6035step0 := by
      have heq : raw6035step0 = (fun i j => raw6035 (permutation43 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6035 permutation43 permutation11
    _ = injectiveMoment H node2390 := by rfl

def raw6036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw6036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical6036 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6036 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw6036 = injectiveMoment H raw6036step0 := by
      have heq : raw6036step0 = (fun i j => raw6036 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6036 permutation11 permutation11
    _ = injectiveMoment H node771 := by rfl

def raw6037 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6037 = injectiveMoment H node2496 := by
  rfl

def raw6038 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical6038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6038 = injectiveMoment H node2497 := by
  rfl

def raw6039 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical6039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6039 = injectiveMoment H node2498 := by
  rfl

def raw6040 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6040 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6040 = injectiveMoment H node2499 := by
  rfl

def raw6041 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6041step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical6041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6041 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw6041 = injectiveMoment H raw6041step0 := by
      have heq : raw6041step0 = (fun i j => raw6041 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6041 permutation11 permutation11
    _ = injectiveMoment H node769 := by rfl

def raw6042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6042 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6042 = injectiveMoment H node894 := by
  rfl

def raw6043 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical6043 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6043 = injectiveMoment H node896 := by
  rfl

def raw6044 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6044step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical6044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6044 = injectiveMoment H node774 := by
  calc
    injectiveMoment H raw6044 = injectiveMoment H raw6044step0 := by
      have heq : raw6044step0 = (fun i j => raw6044 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6044 permutation11 permutation11
    _ = injectiveMoment H node774 := by rfl

def raw6045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical6045 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6045 = injectiveMoment H node897 := by
  rfl

def raw6046 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![1, 2, 0, -3]]

def raw6046step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0], ![4, -1, -3]]

def raw6046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![2, -2, 0], ![-4, 1, 3]]

def raw6046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical6046 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6046 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw6046 = injectiveMoment H raw6046step0 := by
      have heq : raw6046step0 = raw6046.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6046).symm
    injectiveMoment H raw6046step0 = injectiveMoment H raw6046step1 := by
      have heq : raw6046step1 = -raw6046step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6046step0).symm
    injectiveMoment H raw6046step1 = injectiveMoment H raw6046step2 := by
      have heq : raw6046step2 = (fun i j => raw6046step1 (permutation21 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6046step1 permutation21 permutation6
    _ = injectiveMoment H node206 := by rfl

def raw6047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical6047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6047 = injectiveMoment H node898 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
